#!/usr/bin/env python3
"""Compare one definition in two leanexport NDJSON files; needs only Python 3."""
from array import array
from functools import lru_cache
import json
from pathlib import Path
import sys

TARGET = "CEIPalomar.Calculus.consistent"


class Export:
    def __init__(self, stream):
        self.stream = stream
        self.offsets = {"in": array("Q", [0]), "il": array("Q", [0]), "ie": array("Q")}
        pos = 0
        for line in stream:
            row = json.loads(line)
            for key, offsets in self.offsets.items():
                if key in row:
                    if row[key] != len(offsets):
                        raise ValueError(f"nonconsecutive {key} index at byte {pos}")
                    offsets.append(pos)
                    break
            if "def" in row:
                self.last = row["def"]
            pos += len(line)
        # The command exports a single target. Its definition follows its dependencies.
        if not hasattr(self, "last") or self.name(self.last["name"]) != tuple(TARGET.split(".")):
            raise ValueError(f"expected {TARGET} as the final exported definition")

    def node(self, key, number):
        self.stream.seek(self.offsets[key][number])
        row = json.loads(self.stream.readline())
        del row[key]
        (item,) = row.items()
        return item

    @lru_cache(None)
    def name(self, number):
        if number == 0:
            return ()
        tag, arg = self.node("in", number)
        return self.name(arg["pre"]) + (arg["str"] if tag == "str" else arg["i"],)

    @lru_cache(None)
    def level(self, number):
        if number == 0:
            return {"zero": 0}
        tag, arg = self.node("il", number)
        if tag == "param":
            return {tag: self.name(arg)}
        if tag == "succ":
            return {tag: self.level(arg)}
        if tag in {"max", "imax"}:
            return {tag: [self.level(i) for i in arg]}
        raise ValueError(f"unknown level tag {tag}")

    @lru_cache(None)
    def expr(self, number):
        tag, arg = self.node("ie", number)
        if tag == "const":
            arg = {"name": self.name(arg["name"]), "us": [self.level(i) for i in arg["us"]]}
        elif tag == "sort":
            arg = self.level(arg)
        elif tag in {"lam", "forallE", "letE", "app", "proj", "mdata"}:
            arg = dict(arg)
            for key in arg:
                if key in {"type", "body", "value", "fn", "arg", "struct", "expr"}:
                    arg[key] = self.expr(arg[key])
                elif key in {"name", "typeName"}:
                    arg[key] = self.name(arg[key])
        elif tag not in {"bvar", "strVal", "natVal"}:
            raise ValueError(f"unknown expression tag {tag}")
        return {tag: arg}

    def definition(self):
        result = dict(self.last)
        result["name"] = self.name(result["name"])
        for key in ("levelParams", "all"):
            result[key] = [self.name(i) for i in result[key]]
        for key in ("type", "value"):
            result[key] = self.expr(result[key])
        return result


def constants(obj):
    if isinstance(obj, dict):
        if "const" in obj:
            yield ".".join(map(str, obj["const"]["name"]))
        for value in obj.values():
            yield from constants(value)
    elif isinstance(obj, list):
        for item in obj:
            yield from constants(item)


def differences(a, b, path):
    if a == b:
        return
    if isinstance(a, dict) and isinstance(b, dict) and a.keys() == b.keys():
        for k in a:
            yield from differences(a[k], b[k], f"{path}.{k}")
    elif isinstance(a, list) and isinstance(b, list) and len(a) == len(b):
        for i, (x, y) in enumerate(zip(a, b)):
            yield from differences(x, y, f"{path}[{i}]")
    else:
        yield path, a, b


def brief(obj):
    if isinstance(obj, tuple):
        return ".".join(map(str, obj)) or "<anonymous>"
    s = json.dumps(obj, ensure_ascii=False, separators=(",", ":"))
    return s if len(s) <= 420 else s[:417] + "..."


def main():
    if len(sys.argv) != 3:
        sys.exit(f"usage: {Path(sys.argv[0]).name} CHALLENGE.export SOLUTION.export")
    with open(sys.argv[1], "rb") as left, open(sys.argv[2], "rb") as right:
        challenge, solution = Export(left).definition(), Export(right).definition()
    print(TARGET)
    for key, a in challenge.items():
        b = solution[key]
        print(f"{key}: {'equal' if a == b else 'DIFFERS'}")
        if a == b:
            continue
        if key in {"type", "value"}:
            ca, cb = set(constants(a)), set(constants(b))
            print("  constants only in Challenge:", ", ".join(sorted(ca - cb)) or "(none)")
            print("  constants only in Solution:", ", ".join(sorted(cb - ca)) or "(none)")
        for index, (path, x, y) in enumerate(differences(a, b, key)):
            if index == 20:
                print("  further differences omitted")
                break
            print(f"  {path}\n    Challenge: {brief(x)}\n    Solution:  {brief(y)}")


if __name__ == "__main__":
    main()
