#!/bin/bash

if [ $# -eq 0 ]; then
    echo "Usage: $0 <input directory> <output directory>>"
    exit 1
fi

dev_carcara="$HOME/carcara/target/release/carcara"

input_dir=$1
# output_dir=$2
# mkdir -p $output_dir







 nr_steps=0
 nr_total=$(find $current_dir_path -type f -name "*.alethe" | wc -l)
 i=0

 nr_valid=0
 nr_holey=0
 nr_invalid=0
 log_file="$input_dir/log.txt"
find "$input_dir" -type f -name "*.alethe" | while read -r proof_file; do

 file_without_extension="${proof_file%.*}"
 #echo $file_without_extension
 #echo "Processing $(basename $file_without_extension)"
 problem_file="$file_without_extension"".smt2"
 
  

  #Check if file contains steps
  grep "(step" $proof_file | while read -r line ; do
    echo "Processing $line"
   
    i=$(($i + 1))
    # echo $line | grep -op '(step t(\d+(\.\d+)*)' # TODO: fix this to extract the step ID
    step_id=$(echo $line | awk '{print $2}')
    # echo $step_id
    sliced_file_without_extension="$file_without_extension-$step_id"
    sliced_proof_file="$sliced_file_without_extension.alethe"
    sliced_problem_file="$sliced_file_without_extension.smt2"
    eval "$dev_carcara slice $proof_file $problem_file --from $step_id --small > /dev/null"
    # echo "carcara check $sliced_proof_file $sliced_problem_file"
    validity=$(carcara check $sliced_proof_file $sliced_problem_file)
    echo "$proof_file $step_id $validity" >> $log_file
    # if [[ $validity == "valid" ]]
    # then
    #    nr_valid=$(($nr_valid + 1))
    #elif [[ $validity == "holey" ]]
    #then
    #    nr_holey=$(($nr_holey + 1))
    #elif [[ $validity == "invalid" ]]
    #then
    #    nr_invalid=$(($nr_invalid + 1))
    #fi
    done 
done

echo "valid: $(grep valid $log_file | wc -l)"
echo "holey: $(grep holey $log_file | wc -l)"
echo "invalid: $(grep invalid $log_file | wc -l)"

