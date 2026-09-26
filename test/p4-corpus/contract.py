"""Strict versioned corpus observation envelope, separate from published v1."""

import json

SCHEMA = 2
RELATIONS = ("Program_ok", "Program_inst")
PHASES = ("beforeSpec", "afterSpec", "afterSetup", "afterBoot", "after")
MIN_INT = -(1 << 62)
MAX_INT = (1 << 62) - 1
RUN_FIELDS = {"relation", "mode", "cache", "det", "guard", "counterBefore",
              "counterAfterBoot", "counterAfter", "typeFresh", "boot", "result"}


def counter(value):
    return type(value) is int and MIN_INT <= value <= MAX_INT


def validate_run(run, name, adapter):
    if not isinstance(run, dict) or set(run) != RUN_FIELDS:
        raise ValueError("malformed v2 relation envelope")
    base = {key: value for key, value in run.items() if key != "typeFresh"}
    try:
        adapter.validate_run(base, name)
    except SystemExit as error:
        raise ValueError(str(error)) from error
    if not all(counter(run[key]) for key in ("counterBefore", "counterAfterBoot", "counterAfter")):
        raise ValueError("builtin counter outside signed 63-bit range")
    fresh = run["typeFresh"]
    if (not isinstance(fresh, dict) or set(fresh) != set(PHASES)
            or not all(counter(fresh[key]) for key in PHASES)):
        raise ValueError("malformed type-fresh phase counters")
    if run["result"]["class"] == "syntax" and (
            run["counterAfterBoot"] != 0 or run["counterAfter"] != 0):
        raise ValueError("syntax observation consumed builtin counter")


def observation(runs, adapter):
    if not isinstance(runs, dict) or set(runs) != set(RELATIONS):
        raise ValueError("missing/unexpected relation sessions")
    for name in RELATIONS:
        validate_run(runs[name], name, adapter)
    if runs[RELATIONS[0]]["boot"] != runs[RELATIONS[1]]["boot"]:
        raise ValueError("independent sessions booted different values")
    return {"boot": runs[RELATIONS[0]]["boot"],
            "relations": {name: {key: value for key, value in runs[name].items() if key != "boot"}
                          for name in RELATIONS}}


def validate_case(case, adapter):
    if (not isinstance(case, dict) or set(case) != {"schemaVersion", "name", "boot", "relations"}
            or type(case["schemaVersion"]) is not int or case["schemaVersion"] != SCHEMA
            or not isinstance(case["name"], str) or not case["name"]):
        raise ValueError("malformed v2 case envelope")
    if not isinstance(case["relations"], dict):
        raise ValueError("malformed relations")
    if any(not isinstance(run, dict) or set(run) != RUN_FIELDS - {"boot"}
           for run in case["relations"].values()):
        raise ValueError("malformed nested relation fields")
    runs = {name: {**run, "boot": case["boot"]} for name, run in case["relations"].items()
            if isinstance(run, dict)}
    if len(runs) != len(case["relations"]):
        raise ValueError("malformed relation run")
    observation(runs, adapter)


def unsupported_type_fresh(case):
    return any(value != 0 for run in case["relations"].values()
               for value in run["typeFresh"].values())


def strict_json(data):
    """Reject duplicate object keys rather than letting JSON silently keep the last."""
    def object_pairs(pairs):
        obj = {}
        for key, value in pairs:
            if key in obj:
                raise ValueError(f"duplicate JSON key: {key}")
            obj[key] = value
        return obj
    return json.loads(data, object_pairs_hook=object_pairs,
                      parse_constant=lambda value: (_ for _ in ()).throw(
                          ValueError(f"invalid JSON constant {value}")))
