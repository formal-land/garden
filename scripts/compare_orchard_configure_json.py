#!/usr/bin/env python3
import argparse
import json
import sys


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def show(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True)


def main(argv):
    parser = argparse.ArgumentParser()
    parser.add_argument("model")
    parser.add_argument("implementation")
    args = parser.parse_args(argv[1:])

    model = load_json(args.model)
    implementation = load_json(args.implementation)

    ok = True
    for key in ("configure",):
        if model.get(key) != implementation.get(key):
            print("{} mismatch".format(key))
            print("model:          {}".format(show(model.get(key))))
            print("implementation: {}".format(show(implementation.get(key))))
            ok = False

    if ok:
        print("configure JSON comparison succeeded")
        return 0

    print("configure JSON comparison failed")
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
