#!/bin/zsh

# Check if directory is provided
if [[ -z "$1" ]]; then
    echo "Usage: $0 <directory>"
    exit 1
fi

dir="$1"

# Ensure the input is a valid directory
if [[ ! -d "$dir" ]]; then
    echo "Error: '$dir' is not a valid directory."
    exit 1
fi

# Iterate over unique base names in the directory
for file in "$dir"/*.*; do
    base_name="${file%.*}"  # Remove extension
    short_name="${base_name##*/}" # Extract just the base name without path
    target_dir="$dir/$short_name"

    # Create directory if it doesn't exist
    mkdir -p "$target_dir"

    # Move all files with the same base name into the directory
    cp "$base_name".* "$target_dir"/

    # Call another script on the directory (replace 'process_script.sh' with actual script)
    $HOME/carcara/scripts/slice.sh "$target_dir"

done