#!/bin/zsh

#chatgpted
# Executable (replace with the actual path to your executable)
# Trying to use xargs now
proof_path=$1
problem_path=$(awk '{ sub(/.alethe$/, ".smt2", $0); print }') 
slice="echo" #"carcara slice $proof_path $problem_path --single --from " # not done. I'm gonna want to get base to change file extension to smt2

# This awk works to get all step names
# awk 'BEGIN { FS="[ ]"}  /step/ {print $2}' test-proofs/a.alethe

# This here does almost what I want

# awk 'BEGIN { FS="[ ]"}  /step/ {print $2}' test-proofs/a.alethe | xargs -I {} cargo run slice test-proofs/a.alethe test-proofs/a.smt2 --small --from {}

# Actually this one
# awk 'BEGIN { FS="[ ]"}  /step/ {print $2}' test-proofs/a.alethe | xargs -I {} sh -c 'cargo run slice test-proofs/a.alethe test-proofs/a.smt2 --small --from {} > ZZ{}.alethe'

# xargs -r -I@ -a input
# I might loop after all
# Loop through each line in the file

# Here it is
awk 'BEGIN { FS="[ ]"}  /step/ {print $2}' test-proofs/a.alethe | xargs -I {} sh -c 'cargo run slice test-proofs/a.alethe test-proofs/a.smt2 --small --from {} > ZZ{}.alethe && carcara check ZZ{}.alethe test-proofs/a.smt2'



while read -r line; do
    # Check if the line starts with "(step"
    if [[ $line =~ ^\(step[[:space:]]+([^\)]+) ]]; then
        # Extract the name (capture group 1 from the regex)
        step_name="${match[1]}"
        
        # Run the executable with the extracted step name
        # $slice "$step_name"
        echo "$step_name"
    fi
done <$proof_path
