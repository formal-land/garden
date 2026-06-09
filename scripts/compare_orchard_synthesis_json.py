#!/usr/bin/env python3
import argparse
import copy
import json
import sys


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def show(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True)


def normalize_event_rows(event):
    event = copy.deepcopy(event)
    for key in ("row", "from_row"):
        if key in event:
            event[key] = "*"
    for key in ("left", "right"):
        if key in event and isinstance(event[key], dict) and "row" in event[key]:
            event[key]["row"] = "*"
    return event


def compare_events(model, implementation, normalize_rows=False):
    model_events = model.get("events", [])
    implementation_events = implementation.get("events", [])

    if normalize_rows:
        model_events = [normalize_event_rows(event) for event in model_events]
        implementation_events = [
            normalize_event_rows(event) for event in implementation_events
        ]

    if model_events == implementation_events:
        return True

    print(
        "event count: model={} implementation={}".format(
            len(model_events), len(implementation_events)
        )
    )

    for index, (model_event, implementation_event) in enumerate(
        zip(model_events, implementation_events)
    ):
        if model_event != implementation_event:
            print("first event mismatch at index {}".format(index))
            print("model:          {}".format(show(model_event)))
            print("implementation: {}".format(show(implementation_event)))
            return False

    print("one event list is a prefix of the other")
    if len(model_events) > len(implementation_events):
        print(
            "first extra model event: {}".format(
                show(model_events[len(implementation_events)])
            )
        )
    else:
        print(
            "first extra implementation event: {}".format(
                show(implementation_events[len(model_events)])
            )
        )
    return False


def main(argv):
    parser = argparse.ArgumentParser()
    parser.add_argument("model")
    parser.add_argument("implementation")
    parser.add_argument(
        "--normalize-rows",
        action="store_true",
        help="ignore row and from_row fields when comparing events",
    )
    args = parser.parse_args(argv[1:])

    model = load_json(args.model)
    implementation = load_json(args.implementation)

    print("model source: {}".format(model.get("source")))
    print("implementation source: {}".format(implementation.get("source")))

    ok = True
    for key in ("schema",):
        if model.get(key) != implementation.get(key):
            print("{} mismatch".format(key))
            print("model:          {}".format(show(model.get(key))))
            print("implementation: {}".format(show(implementation.get(key))))
            ok = False

    if args.normalize_rows:
        print("row normalization: enabled")

    ok = compare_events(model, implementation, args.normalize_rows) and ok

    if ok:
        print("synthesis JSON comparison succeeded")
        return 0

    print("synthesis JSON comparison failed")
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
