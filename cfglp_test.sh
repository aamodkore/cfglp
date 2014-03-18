for file in `ls $1/*.cfg`;
do
    echo "Diff for " $file ": "
    ./cfglp $file $4 $2 $3;
    mv $file.ic act.ic.out;
    mv $file.spim act.spim.out;	   
    ./cfglp64 $file $4 $2 $3;
    mv $file.ic exp.ic.out;
    mv $file.spim exp.spim.out;	
    diff -b -B act.ic.out exp.ic.out;
    diff -b -B act.spim.out exp.spim.out;
    rm -rf *.*.out ;
done

