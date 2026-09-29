"""Complete Nano STF session observations: contract, compact storage and validation.

Each of the pinned corpus's STF sessions is recorded from the pinned upstream AL simulator
with guards, caches and deterministic checking off: the initialization outcome and context,
then every driven packet with its outcome, forwarding decision, transmissions and resulting
context and architecture state. Values are stored once in a shared table and referenced by
index. Their `vid`/`vhash` note fields are upstream cache identities, not semantics, and are
normalized to 0; source regions are normalized to checkout-independent paths.
"""

import gzip
import hashlib
import io
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
from P4SpecTecTest.Oracle.P4.Replay.capture import typed_value  # noqa: E402

FIXTURE = pathlib.Path(__file__).with_name("sessions-observed.json")
UPSTREAM = "8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3"
NANO_SPEC = "60dfd9912011bd5b1746ac88b26b58f7b3981991"
COMPRESSED_LIMIT = 4 * 1024 * 1024
EXPANDED_LIMIT = 256 * 1024 * 1024
OUTCOMES = {"pass", "runtimeFail"}


def strict_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def strict_json(data):
    return json.loads(data, object_pairs_hook=strict_object,
                      parse_constant=lambda value: (_ for _ in ()).throw(
                          ValueError(f"nonfinite JSON constant: {value}")))


def strip_identities(value):
    """Zero upstream cache identities in value notes; ExternV payloads are data."""
    if isinstance(value, list):
        return [strip_identities(item) for item in value]
    if isinstance(value, dict):
        result = {}
        for key, item in value.items():
            if key == "note" and isinstance(item, dict) and set(item) == {"vid", "typ", "vhash"}:
                result[key] = {"vid": 0, "typ": strip_identities(item["typ"]), "vhash": 0}
            elif key == "it" and isinstance(item, list) and item[:1] == ["ExternV"]:
                result[key] = item
            else:
                result[key] = strip_identities(item)
        return result
    return value


def packet(value):
    return (isinstance(value, list) and len(value) == 2 and type(value[0]) is int
            and -(2**62) <= value[0] < 2**62 and isinstance(value[1], str)
            and all(ord(c) < 128 for c in value[1]))


def digest(value):
    return (isinstance(value, str) and len(value) == 64
            and all(c in "0123456789abcdef" for c in value))


def validate(bundle):
    """Reject any shape the Lean replay would otherwise have to interpret."""
    expected = {"schemaVersion", "upstreamRevision", "nanoSpecRevision", "mode", "cache",
                "det", "guard", "values", "sessions"}
    if set(bundle) != expected or bundle["schemaVersion"] != 1:
        raise ValueError("wrong session fixture schema")
    if (bundle["upstreamRevision"] != UPSTREAM or bundle["nanoSpecRevision"] != NANO_SPEC
            or bundle["mode"] != "AL" or bundle["cache"] is not False
            or bundle["det"] is not False or bundle["guard"] is not False):
        raise ValueError("wrong session provenance or configuration")
    values = bundle["values"]
    if not isinstance(values, list) or not all(typed_value(v) for v in values):
        raise ValueError("malformed value table")
    if len({json.dumps(v, sort_keys=True) for v in values}) != len(values):
        raise ValueError("duplicate value table entry")

    def ref(n):
        return type(n) is int and 0 <= n < len(values)

    sessions = bundle["sessions"]
    if not isinstance(sessions, list) or not sessions:
        raise ValueError("missing sessions")
    ids = [s.get("id") for s in sessions]
    if len(set(ids)) != len(ids):
        raise ValueError("duplicate session identity")
    for s in sessions:
        keys = {"id", "program", "programSha256", "stf", "stfSha256", "export",
                "stfResult", "init", "drives"}
        if set(s) != keys or not isinstance(s["id"], str) or not s["id"].startswith(
                "corpus:packet:"):
            raise ValueError("wrong session identity fields")
        if not (digest(s["programSha256"]) and digest(s["stfSha256"])):
            raise ValueError("malformed session source digest")
        if s["stfResult"] not in {"pass", "runtimeFail", "syntaxFail"}:
            raise ValueError("unknown STF result")
        init = s["init"]
        if not isinstance(init, dict) or init.get("class") not in OUTCOMES:
            raise ValueError("malformed initialization outcome")
        if init["class"] == "pass":
            if set(init) != {"class", "ctx", "arch"} or not (ref(init["ctx"])
                                                             and ref(init["arch"])):
                raise ValueError("malformed initialization values")
        elif set(init) != {"class"} or s["drives"]:
            raise ValueError("failed initialization cannot drive packets")
        drives = s["drives"]
        if not isinstance(drives, list):
            raise ValueError("malformed drives")
        for index, d in enumerate(drives):
            if not isinstance(d, dict) or d.get("class") not in OUTCOMES or not packet(
                    d.get("rx")):
                raise ValueError("malformed drive")
            if d["class"] == "pass":
                if (set(d) != {"rx", "class", "ctx", "arch", "decision", "txs"}
                        or not (ref(d["ctx"]) and ref(d["arch"]) and ref(d["decision"]))
                        or not isinstance(d["txs"], list)
                        or not all(packet(t) for t in d["txs"])):
                    raise ValueError("malformed passing drive")
            else:
                if set(d) != {"rx", "class"} or index != len(drives) - 1:
                    raise ValueError("a failing drive ends its session")


def read():
    with FIXTURE.with_suffix(".json.gz").open("rb") as stream:
        packed = stream.read(COMPRESSED_LIMIT + 1)
    if len(packed) > COMPRESSED_LIMIT:
        raise ValueError("session fixture compressed size exceeds bound")
    with gzip.GzipFile(fileobj=io.BytesIO(packed)) as stream:
        data = stream.read(EXPANDED_LIMIT + 1)
    if len(data) > EXPANDED_LIMIT:
        raise ValueError("session fixture expanded size exceeds bound")
    sha = hashlib.sha256(data).hexdigest()
    if FIXTURE.with_suffix(".json.sha256").read_text() != f"{sha}  {FIXTURE.name}\n":
        raise ValueError("session fixture checksum mismatch")
    bundle = strict_json(data)
    validate(bundle)
    return bundle, data


def write(bundle):
    """Publish observations compactly without removing any validated field."""
    validate(bundle)
    data = json.dumps(bundle, separators=(",", ":"), sort_keys=True).encode() + b"\n"
    sys.path.insert(0, str(ROOT / "scripts"))
    import importlib.util
    spec = importlib.util.spec_from_file_location("snapshot", ROOT / "scripts/spec-snapshot.py")
    snapshot = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(snapshot)
    snapshot.atomic_write(FIXTURE.with_suffix(".json.gz"), gzip.compress(data, mtime=0))
    sha = hashlib.sha256(data).hexdigest()
    snapshot.atomic_write(FIXTURE.with_suffix(".json.sha256"),
                          f"{sha}  {FIXTURE.name}\n".encode())
