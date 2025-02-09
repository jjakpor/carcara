#!/bin/bash

if [ $# -eq 0 ]; then
    echo "Usage: $0 <input directory> <output directory>>"
    exit 1
fi

dev_carcara="$HOME/carcara/target/release/carcara"

input_dir=$1
output_dir="$2"
mkdir -p $output_dir

nr_steps=0
nr_total_files=$(find $input_dir -type f -name "*.alethe" | wc -l)
echo "Found $nr_total_files"

nr_valid_total=0
nr_holey_total=0
nr_invalid_total=0

#TODO: Copy the whole directory structure if in_dir in out_dir
find "$input_dir" -type f -name "*.alethe" | while read -r proof_file; do

 nr_valid=0
 nr_holey=0
 nr_invalid=0

 base_name="${proof_file%.*}"  # Remove extension
 echo "base_name $base_name"
 
 short_name="${base_name##*/}" # Extract just the base name without path
 target_dir="$output_dir/$base_name"

 # Create directory if it doesn't exist
 mkdir -p "$target_dir"

 log_file="$input_dir/log.txt"

 problem_file="$base_name"".smt2"
 echo "problem_file: $problem_file"
 i=0

 #loop over all steps
while read -r line ; do
    #echo "Processing $line"
    i=$(($i + 1))
    step_id=$(echo $line | awk '{print $2}')
    echo "$step_id"
    sliced_file_without_extension="$target_dir"/"$short_name-$step_id"
    sliced_proof_file="$sliced_file_without_extension.alethe"
    sliced_problem_file="$sliced_file_without_extension.smt2"
    #TODO: Have slice take in another argument (or two) with output directory or both new problem and new proof file
    eval "$dev_carcara slice $proof_file $problem_file --from $step_id --small > /dev/null"
    mv "$base_name""-$step_id.smt2" "$target_dir"
    mv "$base_name""-$step_id.alethe" "$target_dir"

    validity=$(carcara check $sliced_proof_file $sliced_problem_file -i)
    return_valid=$?
    echo $validity
    echo $return_valid
    if [ $return_valid = 0 ] ;
    then
      nr_valid=$(($nr_valid + 1))
    elif [ $validity = "holey" ]
    then
      holey=$(($holey + 1))
    fi
    echo "$proof_file $step_id $validity" >> $log_file
    
done <<<  $( grep "(step" $proof_file )
echo "For file $proof_file there were $i steps. Of these $nr_valid were valid after slicing"
done

echo "valid: $(grep -w valid $log_file | wc -l)" >> $log_file
echo "holey: $(grep -w holey $log_file | wc -l)" >> $log_file
echo "invalid: $(grep -w invalid $log_file | wc -l)" >> $log_file

