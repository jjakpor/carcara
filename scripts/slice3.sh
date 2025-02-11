#!/bin/zsh

if [ $# -eq 0 ]; then
    echo "Usage: $0 <input directory> <output directory>"
    exit 1
fi

dev_carcara="$HOME/carcara/target/release/carcara"

input_dir=$1
output_dir="$2"
mkdir -p "$output_dir"

nr_steps=0


# Initialize totals
nr_valid_total=0
nr_holey_total=0
nr_invalid_total=0

log_file="$input_dir/log.txt"
> "$log_file"  # Clear the log file at the start

# Avoid subshell by using process substitution
while read -r proof_file; do
    nr_valid=0
    nr_holey=0
    nr_invalid=0

    base_name="${proof_file%.*}"
    short_name="${base_name##*/}"
    target_dir="$output_dir/$base_name"

    mkdir -p "$target_dir"
    problem_file="${base_name}.smt2"

    i=0
    while read -r line; do
        i=$((i + 1))
        echo $i
        step_id=$(echo "$line" | awk '{print $2}')
        sliced_file_without_extension="$target_dir/$short_name-$step_id"
        sliced_proof_file="$sliced_file_without_extension.alethe"
        sliced_problem_file="$sliced_file_without_extension.smt2"

        eval "$dev_carcara slice $proof_file $problem_file --from $step_id --small > /dev/null"
        mv "$base_name-$step_id.smt2" "$target_dir"
        mv "$base_name-$step_id.alethe" "$target_dir"

        validity=$(carcara check "$sliced_proof_file" "$sliced_problem_file" -i | awk '{print $1}')
        return_valid=$?

        if [ $return_valid -eq 0 ]; then
            nr_valid=$((nr_valid + 1))
        elif [ "$validity" = "holey" ]; then
            nr_holey=$((nr_holey + 1))
        else
            nr_invalid=$((nr_invalid + 1))
        fi

        echo "$proof_file $step_id $validity" >> "$log_file"
    done < <(grep "(step" "$proof_file")

    echo "For file $proof_file there were $i steps. Of these $nr_valid were valid after slicing"

    # Update global totals **outside the subshell**
    nr_valid_total=$((nr_valid_total + nr_valid))
    nr_holey_total=$((nr_holey_total + nr_holey))
    nr_invalid_total=$((nr_invalid_total + nr_invalid))

done < <(find "$input_dir" -type f -name "*.alethe")


nr_total_files=$(find "$input_dir" -type f -name "*.alethe" | wc -l)
echo "Found $nr_total_files"
echo "valid: $nr_valid_total"
echo "holey: $nr_holey_total"
echo "invalid: $nr_invalid_total"
