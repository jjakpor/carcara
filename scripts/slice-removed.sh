
    if ! [ $rule_name = "evaluate" ] && ! [ $rule_name = "eq-symm" ]
    then
      new_proof_path=$new_dir/$(basename $file_without_extension)"_"$i".alethe"
      echo "unsat" > $new_proof_path
      echo "(assume a0 false)" >> $new_proof_path
      echo $line >> $new_proof_path
      echo "(step u0 (cl (not false)) :rule false)" >> $new_proof_path
      echo "(step u1 (cl) :rule resolution :premises (a0 u0))" >> $new_proof_path

      new_problem_path=$new_dir/$(basename $file_without_extension)"_"$i".smt2"
      sed '0,/assert.*/{s/assert.*/assert false\)/}' $problem_file > $new_problem_path
      #sed '2,/(assert.*/{s/(assert.*//}' $new_problem_path
      awk '/assert.*/&&c++>0 {next} 1' $new_problem_path > testfile.tmp && mv testfile.tmp $new_problem_path


      echo "{\"benchmark_name\": \"" $(basename $file_without_extension)"_"$i"\", \"rewrite_rule\": \"$rule_name\"}," >> $rewrites_file



      #sed -e ':begin;s/assert//2;t begin' $new_problem_path

    fi
