#!/usr/bin/env python3
import json
import sys


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def show(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True)


def compare_events(model, implementation):
    model_events = model.get("events", [])
    implementation_events = implementation.get("events", [])

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
    if len(argv) != 3:
        print(
            "usage: compare_orchard_synthesis_json.py MODEL.json IMPLEMENTATION.json",
            file=sys.stderr,
        )
        return 2

    model = load_json(argv[1])
    implementation = load_json(argv[2])

    print("model source: {}".format(model.get("source")))
    print("implementation source: {}".format(implementation.get("source")))

    ok = True
    for key in ("schema", "event_default"):
        if model.get(key) != implementation.get(key):
            print("{} mismatch".format(key))
            print("model:          {}".format(show(model.get(key))))
            print("implementation: {}".format(show(implementation.get(key))))
            ok = False

    ok = compare_events(model, implementation) and ok

    if ok:
        print("synthesis JSON comparison succeeded")
        return 0

    print("synthesis JSON comparison failed")
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
