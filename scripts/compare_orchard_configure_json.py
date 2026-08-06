#!/usr/bin/env python3
import argparse
import json
import sys


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def show(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True)


def query_view(entries):
    return [
        {
            "column": entry["column"]["index"],
            "rotation": entry["rotation"],
        }
        for entry in entries
    ]


def column_view(column):
    return {"kind": column["kind"], "index": column["index"]}


def implementation_vk_metadata(highlevel, compression):
    configure = highlevel["configure"]
    selector_count = configure["selectors"]["count"]
    selector_types = [None] * selector_count
    for assignment in compression["assignments"]:
        selector = assignment["selector"]
        simple = assignment["simple"]
        previous = selector_types[selector]
        if previous is not None and previous != simple:
            raise ValueError("inconsistent selector kind for {}".format(selector))
        selector_types[selector] = simple
    if any(simple is None for simple in selector_types):
        missing = [
            index for index, simple in enumerate(selector_types) if simple is None
        ]
        raise ValueError("selector kinds missing from compression: {}".format(missing))

    lookup_fixed_columns = []
    for lookup in configure["lookups"]:
        for expression in lookup["table_expressions"]:
            column = expression["expression"]["column"]
            index = column["index"]
            if index not in lookup_fixed_columns:
                lookup_fixed_columns.append(index)

    return {
        "valid": True,
        "columns": configure["columns"],
        "selector_types": selector_types,
        "lookup_fixed_columns": lookup_fixed_columns,
        "advice_queries": query_view(configure["advice_queries"]),
        "fixed_queries": query_view(configure["fixed_queries"]),
        "instance_queries": query_view(configure["instance_queries"]),
        "permutation_columns": [
            column_view(column) for column in configure["permutation"]["columns"]
        ],
        "constants": [
            entry["column"]["index"] for entry in configure["constants"]
        ],
        "minimum_degree": configure["minimum_degree"],
    }


def main(argv):
    parser = argparse.ArgumentParser()
    parser.add_argument("model")
    parser.add_argument("implementation")
    parser.add_argument("--implementation-highlevel")
    parser.add_argument("--selector-compression")
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

    if bool(args.implementation_highlevel) != bool(args.selector_compression):
        parser.error(
            "--implementation-highlevel and --selector-compression must be used together"
        )

    if args.implementation_highlevel:
        highlevel = load_json(args.implementation_highlevel)
        compression = load_json(args.selector_compression)
        expected_metadata = implementation_vk_metadata(highlevel, compression)
        if model.get("vk_metadata") != expected_metadata:
            print("vk_metadata mismatch")
            print("model:          {}".format(show(model.get("vk_metadata"))))
            print("implementation: {}".format(show(expected_metadata)))
            ok = False

    if ok:
        print("configure JSON comparison succeeded")
        return 0

    print("configure JSON comparison failed")
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
