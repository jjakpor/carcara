#!/bin/zsh

# Check if the correct number of arguments is given

# Input directory and executable
input_dir="$1"

# Check if the input directory exists
if [ ! -d "$input_dir" ]; then
    echo "Error: Directory '$input_dir' does not exist."
    exit 1
fi

# Create an associative array to group files by their number
declare -A file_groups

# Iterate over the files in the input directory
for file in "$input_dir"/*; do
    if [ -f "$file" ]; then
        # Extract the base filename (e.g., "file1.a" -> "file1")
        base_name=$(basename "$file")
        group_name="${base_name%.*}"  # Remove the extension

        # Extract the numeric part (e.g., from "file1.a", get "file1")
        group_key=$(echo "$group_name" | grep -oE '^[a-zA-Z0-9]+')

        # Store the file in the corresponding group
        file_groups["$group_key"]+="$file "
    fi
done

# Process each group
for group in ${(k)file_groups}; do
    # Create a directory for the group
    new_dir="$input_dir/${group}_dir"
    mkdir -p "$new_dir"

    # Move the files into the group's directory
    for file in ${(z)file_groups[$group]}; do
        cp "$file" "$new_dir"
    done

    # Run the executable on the new directory
    "$HOME/carcara/scripts/slice.sh" "$(realpath $new_dir)"
done

echo "Operation complete."
