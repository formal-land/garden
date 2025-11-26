import os

SOURCE_DIR = "../third-party/brevis/vm/src"
DEST_DIR = "Brevis"

def main():
    # Ensure destination directory exists
    if not os.path.exists(DEST_DIR):
        print(f"Creating directory: {DEST_DIR}")
        os.makedirs(DEST_DIR)

    print(f"Scanning {SOURCE_DIR} for Rust files...")

    count = 0
    for root, dirs, files in os.walk(SOURCE_DIR):
        for file_name in files:
            if file_name.endswith(".rs"):
                # Source file path
                source_path = os.path.join(root, file_name)
 
                # Calculate relative path from SOURCE_DIR to current file
                rel_path_from_source_root = os.path.relpath(source_path, SOURCE_DIR)

                # Destination path
                dest_path = os.path.join(DEST_DIR, rel_path_from_source_root)

                # Ensure destination subdirectory exists
                dest_subdir = os.path.dirname(dest_path)
                if not os.path.exists(dest_subdir):
                    os.makedirs(dest_subdir)

                # Calculate relative path for the symlink
                # We want the link to be relative so it works if the repo is moved
                abs_source = os.path.abspath(source_path)
                abs_dest_dir = os.path.abspath(os.path.dirname(dest_path))

                rel_source = os.path.relpath(abs_source, abs_dest_dir)

                try:
                    if os.path.islink(dest_path):
                        os.remove(dest_path)
                    elif os.path.exists(dest_path):
                        print(f"Warning: {dest_path} exists and is not a symlink. Skipping.")
                        continue

                    os.symlink(rel_source, dest_path)
                    # print(f"Linked {rel_path_from_source_root} -> {rel_source}")
                    count += 1
                except OSError as e:
                    print(f"Error linking {rel_path_from_source_root}: {e}")

    print(f"Finished. Created {count} symlinks.")

if __name__ == "__main__":
    main()
