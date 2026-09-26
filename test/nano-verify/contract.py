"""Offline contract for the bounded shared-verify observations."""

import importlib.util
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


strict = load("verify_strict_json", ROOT / "test/nano-target/fixture.py").strict_json
typed_value = load("verify_value_contract", ROOT / "scripts/export-p4-oracle.py").typed_value


def validate(bundle, requests):
    if (set(bundle) != {"upstreamRevision", "nanoSpecRevision", "scope", "cases",
                       "nanoReachability"}
            or bundle["upstreamRevision"] != "8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3"
            or bundle["nanoSpecRevision"] != "60dfd9912011bd5b1746ac88b26b58f7b3981991"
            or bundle["scope"] != "shared-verify-and-nano-dispatch"):
        raise ValueError("wrong verify provenance")
    if not isinstance(bundle["cases"], list) or len(bundle["cases"]) != 19:
        raise ValueError("wrong case count")
    if [c.get("request") for c in bundle["cases"]] != requests:
        raise ValueError("request identity differs")
    for case in bundle["cases"]:
        if set(case) != {"request", "result"}:
            raise ValueError("wrong case shape")
        r = case["result"]
        fields = {"class", "calls", "counterAfter"}
        if r["class"] == "pass":
            fields.add("outputs")
            if (not isinstance(r["outputs"], list) or len(r["outputs"]) != 3
                    or not all(typed_value(v) for v in r["outputs"])):
                raise ValueError("malformed outputs")
        elif r["class"] == "runtimeError":
            fields.add("message")
            if not isinstance(r["message"], str) or not r["message"]:
                raise ValueError("malformed runtime diagnostic")
        elif r["class"] not in {"abort", "unmatch"}:
            raise ValueError("unknown outcome")
        if set(r) != fields or not isinstance(r["calls"], list):
            raise ValueError("wrong observation shape")
        if (type(r["counterAfter"]) is not int or not 0 <= r["counterAfter"] <= 2
                or r["counterAfter"] != len(r["calls"])):
            raise ValueError("wrong callback counter")
        for call in r["calls"]:
            if (set(call) != {"name", "types", "args"} or call["name"] != "find_var_e"
                    or call["types"] != [] or not isinstance(call["args"], list)
                    or len(call["args"]) != 3 or not all(typed_value(v) for v in call["args"])):
                raise ValueError("malformed callback")
    if bundle["nanoReachability"] != {
            "externRelations": ["ExternMethodCall_eval"], "mode": "AL",
            "cache": False, "det": False, "guard": False, "fullP4GetterAgainstNano": "unmatch",
            "counterBefore": 0, "counterAfter": 0}:
        raise ValueError("Nano reachability boundary differs")
    for key in ("cache", "det", "guard"):
        if bundle["nanoReachability"][key] is not False:
            raise ValueError("malformed interpreter configuration")
    for key in ("counterBefore", "counterAfter"):
        if type(bundle["nanoReachability"][key]) is not int:
            raise ValueError("malformed boundary counter")


def read():
    with (ROOT / "test/nano-verify/observed.json").open("rb") as stream:
        raw = stream.read(1024 * 1024 + 1)
    if len(raw) > 1024 * 1024:
        raise ValueError("verify fixture exceeds bound")
    bundle = strict(raw)
    requests = strict((ROOT / "test/nano-verify/requests.json").read_bytes())
    validate(bundle, requests)
    return bundle, requests
