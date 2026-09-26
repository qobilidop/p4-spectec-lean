"""Bounded packet fixture contract and lossless storage, without upstream execution."""

import gzip
import hashlib
import importlib.util
import io
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
PACKET = ROOT / "test/nano-target/packet-observed.json"
CASES = [("free-pass", False, "pass", 1), ("field-access", False, "pass", 2),
         ("action-call-table-2", False, "pass", 3), ("field-access", True, "runtimeFail", 1)]
# Independently SHA-256 hashed from `git show 8c8e0c6:<path>`, not copied from
# the observation envelope. The full source path is fixed by CASES above.
SOURCE_HASHES = {
    "free-pass": (
        "d229aadd79ab80a25d4cfcbe070386a074270028754d5d00eea60e421a36cb4e",
        "964bd4d304a4092507ed85097bc635f0a9f87ca46382620f00e40ff6ed3f686d"),
    "field-access": (
        "4eaa5e8062d38f8b75b0c2061b4102aacb23c2e2c67c4464a759db91938faf98",
        "78e9231d06445dbb759d088bdbcea4b9df613155dfd6c6c220947f21d040941d"),
    "action-call-table-2": (
        "95cc6c1e235aeeffb01078afac327d984e27452efc119106069960324633a091",
        "20c3969d22e99ea72a8d9191e62344a1d367ae05cf91ad35d0b304e8c1090077"),
}


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate(bundle):
    expected = {"schemaVersion", "upstreamRevision", "nanoSpecRevision", "mode",
                "cache", "det", "relation", "cases"}
    if (set(bundle) != expected or type(bundle["schemaVersion"]) is not int
            or bundle["schemaVersion"] != 2):
        raise ValueError("wrong packet fixture schema")
    if (bundle["upstreamRevision"] != "8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3"
            or bundle["nanoSpecRevision"] != "60dfd9912011bd5b1746ac88b26b58f7b3981991"
            or bundle["mode"] != "AL" or bundle["relation"] != "NanoSwitch_drive"
            or bundle["cache"] is not False or bundle["det"] is not False):
        raise ValueError("wrong packet provenance/configuration")
    if not isinstance(bundle["cases"], list) or len(bundle["cases"]) != len(CASES):
        raise ValueError("wrong packet case count")
    oracle = load("packet_value_contract", ROOT / "scripts/export-p4-oracle.py")
    for case, (name, guard, outcome, count) in zip(bundle["cases"], CASES):
        prefix = "nano-p4/testdata/positive/" + name
        if (set(case) != {"program", "programSha256", "stf", "stfSha256",
                         "guard", "observation"}
                or case["program"] != prefix + ".p4" or case["stf"] != prefix + ".stf"
                or case["guard"] is not guard):
            raise ValueError("wrong packet case identity")
        for key in ("programSha256", "stfSha256"):
            digest = case[key]
            if (not isinstance(digest, str) or len(digest) != 64
                    or any(c not in "0123456789abcdef" for c in digest)):
                raise ValueError("malformed source digest")
        if (case["programSha256"], case["stfSha256"]) != SOURCE_HASHES[name]:
            raise ValueError("source digest differs from pinned Git object")
        observation = case["observation"]
        if (set(observation) != {"stfResult", "events", "driverEvents"}
                or observation["stfResult"] != outcome
                or not isinstance(observation["events"], list)
                or not isinstance(observation["driverEvents"], list)
                or len(observation["events"]) != count
                or len(observation["driverEvents"]) != count):
            raise ValueError("wrong packet observation shape")
        for driver, event in ([(False, e) for e in observation["events"]]
                              + [(True, e) for e in observation["driverEvents"]]):
            fields = {"class", "inputs", "counterBefore", "counterAfter"}
            if driver:
                fields.add("rx")
            if outcome == "pass":
                fields.add("outputs")
                if driver:
                    fields.add("txs")
            if set(event) != fields or event["class"] != outcome:
                raise ValueError("wrong packet event class")
            for key in ("counterBefore", "counterAfter"):
                n = event[key]
                if type(n) is not int or not -(2**62) <= n < 2**62:
                    raise ValueError("out-of-range fresh counter")
            for key in ("inputs", "outputs") if outcome == "pass" else ("inputs",):
                values = event[key]
                if (not isinstance(values, list) or len(values) != 2
                        or not all(oracle.typed_value(v) for v in values)):
                    raise ValueError("malformed typed packet values")
            if driver:
                packets = [event["rx"]]
                if outcome == "pass":
                    if not isinstance(event["txs"], list):
                        raise ValueError("malformed driver transmissions")
                    packets += event["txs"]
                for packet in packets:
                    if (not isinstance(packet, list) or len(packet) != 2
                            or type(packet[0]) is not int
                            or not -(2**62) <= packet[0] < 2**62
                            or not isinstance(packet[1], str)
                            or any(ord(c) > 127 for c in packet[1])):
                        raise ValueError("malformed driver packet")


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


def read():
    with PACKET.with_suffix(".json.gz").open("rb") as stream:
        packed = stream.read(1024 * 1024 + 1)
    if len(packed) > 1024 * 1024:
        raise ValueError("packet fixture compressed size exceeds bound")
    with gzip.GzipFile(fileobj=io.BytesIO(packed)) as stream:
        data = stream.read(16 * 1024 * 1024 + 1)
    if len(data) > 16 * 1024 * 1024:
        raise ValueError("packet fixture expanded size exceeds bound")
    digest = hashlib.sha256(data).hexdigest()
    if PACKET.with_suffix(".json.sha256").read_text() != f"{digest}  {PACKET.name}\n":
        raise ValueError("packet fixture checksum mismatch")
    bundle = strict_json(data)
    validate(bundle)
    return bundle, data


def write(bundle):
    """Publish generated observations compactly without removing any JSON field."""
    validate(bundle)
    data = json.dumps(bundle, separators=(",", ":"), sort_keys=True).encode() + b"\n"
    snapshot = load("packet_snapshot", ROOT / "scripts/spec-snapshot.py")
    snapshot.atomic_write(PACKET.with_suffix(".json.gz"), gzip.compress(data, mtime=0))
    digest = hashlib.sha256(data).hexdigest()
    snapshot.atomic_write(PACKET.with_suffix(".json.sha256"),
                          f"{digest}  {PACKET.name}\n".encode())
