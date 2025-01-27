dev_carcara="$HOME/carcara/target/release/carcara"

input_dir=$1
 nr_total=$(find $current_dir_path -type f -name "*.alethe" | wc -l)
 nr_valid=0
 nr_holey=0
 nr_invalid=0
 log_file="$input_dir/log.txt"



while read -r proof_file; do

    file_without_extension="${proof_file%.*}"
    problem_file="$file_without_extension"".smt2"

    while read -r line; do
        echo "Processing $line"
        step_id=$(echo $line | awk '{print $2}')
        echo $step_id
        sliced_file_without_extension="$file_without_extension-$step_id"
        sliced_proof_file="$sliced_file_without_extension.alethe"
        sliced_problem_file="$sliced_file_without_extension.smt2"
        eval "$dev_carcara slice $proof_file $problem_file --from $step_id --small > /dev/null"
        echo "carcara check $sliced_proof_file $sliced_problem_file"
        validity=$(carcara check $sliced_proof_file $sliced_problem_file)
        echo "$proof_file $step_id $validity" >> $log_file
        if [[ $validity == "valid" ]]; then
            nr_valid=$(($nr_valid + 1))
        elif [[ $validity == "holey" ]]; then
            nr_holey=$(($nr_holey + 1))
        elif [[ $validity == "invalid" ]]; then
            nr_invalid=$(($nr_invalid + 1))
        fi
    done < <(grep "(step" "$proof_file")
done < <(find "$input_dir" -type f -name "*.alethe")
