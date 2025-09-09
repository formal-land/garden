import os
import subprocess
import json


def process_json_files(input_dir, output_dir, command):
    """Recursively processes JSON files in a directory and runs a command on them.

    Args:
        input_dir: The input directory containing JSON files.
        output_dir: The output directory to store the processed files.
        command: The command to run on each JSON file (as a list of strings).
    """

    for root, _, files in os.walk(input_dir):
        for filename in files:
            if filename.endswith(".json"):
                # Check if there is a corresponding ".circom" file
                circom_filename = os.path.splitext(filename)[0] + ".circom"
                if circom_filename not in files:
                    continue
                input_path = os.path.join(root, filename)
                relative_path = os.path.relpath(input_path, input_dir)
                output_path = os.path.join(output_dir, os.path.splitext(relative_path)[0] + ".v")

                os.makedirs(os.path.dirname(output_path), exist_ok=True)

                try:
                    with open(input_path, 'r') as f:
                        json.load(f)
                except json.JSONDecodeError as e:
                    print(f"Error decoding JSON in {input_path}: {e}")
                    continue

                try:
                    with open(output_path, "w") as outfile:
                        subprocess.run(command + [input_path], stdout=outfile, check=True, text=True)
                    print(f"Processed: {input_path} -> {output_path}")
                except subprocess.CalledProcessError as e:
                    print(f"Error executing command on {input_path}: {e}")
                except FileNotFoundError:
                    print(f"Command not found: {command[0]}")


input_directory = "third-party/circomlib"
output_directory = "Garden/Circom/Circomlib/translation"
your_command = ["python", "scripts/rocq_of_circom.py"]

process_json_files(input_directory, output_directory, your_command)
