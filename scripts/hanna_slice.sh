#!/bin/zsh

if [ $# -eq 0 ]; then
    echo "Usage: $0 <input directory> <output directory>"
    exit 1
fi

dev_carcara="$HOME/Jibiana/carcara/target/release-lto/carcara"

input_dir=$1
output_dir="$2"
mkdir -p "$output_dir"

nr_steps=0


nr_valid_total=0
nr_holey_total=0
nr_invalid_total=0

log_file="$output_dir/log.txt"


 while read -r proof_file; do
    nr_valid=0
    nr_holey=0
    nr_invalid=0

    base_name="${proof_file%.*}"  # Remove extension
    # echo "base_name $base_name"

    short_name="${base_name##*/}" # Extract just the base name without path
    target_dir="$output_dir/$base_name"

    mkdir -p "$target_dir"

    problem_file="${base_name}.smt2"
    echo "problem_file: $problem_file"
    i=0

    # Loop over all steps
    while read -r line; do
        i=$((i + 1))
        step_id=$(echo "$line" | awk '{print $2}')
        # echo "$step_id"
        sliced_file_without_extension="$target_dir/$short_name-$step_id"
        sliced_proof_file="$sliced_file_without_extension.alethe"
        sliced_problem_file="$sliced_file_without_extension.smt2"

	#Use carcara to slice the step
        slice=$($dev_carcara slice $proof_file $problem_file --from $step_id --small 2>&1)
        if [ $? = 0 ]; then
	  new_file_name="$base_name-$step_id"

	  #Use carcara to check the new problem and proof
          validity=$($dev_carcara check "$new_file_name.alethe" "$new_file_name.smt2" -i 2>&1)
        
	  #echo "$validity"
        

          if [ "$validity" = "valid" ]; then
            nr_valid=$((nr_valid + 1))
          elif [ "$validity" = "holey" ]; then
            nr_holey=$((nr_holey + 1))
          else
	    echo "$validity"
            cp "$new_file_name.smt2" "$target_dir"
            cp "$new_file_name.alethe" "$target_dir"
            nr_invalid=$((nr_invalid + 1))
          fi

	  rm "$new_file_name.smt2"
  	  rm "$new_file_name.alethe"

          echo "$proof_file, $step_id, $validity, $carcara_error" >> "$log_file"
        else
	  echo "Step $step_id could not be sliced $proof_file"
	fi
    done < <(grep "(step" "$proof_file")  # <- Process substitution fixes the issue

    echo "For file $proof_file there were $i steps. Of these $nr_valid were valid after slicing"

    nr_valid_total=$((nr_valid_total + nr_valid))
    nr_holey_total=$((nr_holey_total + nr_holey))
    nr_invalid_total=$((nr_invalid_total + nr_invalid))
done <<< $(find "$input_dir" -type f -name "*.alethe") 

# Output final totals
echo "valid: $nr_valid_total"
echo "holey: $nr_holey_total"
echo "invalid: $nr_invalid_total"

