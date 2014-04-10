for file in `ls $1/*.cfg`;
do
    echo "Diff for " $file ": "
    ./cfglp $file $2 $3 $4 $5 $6;
    mv $file.sym act.sym.out;
    mv $file.spim act.spim.out;	   
    mv $file.ic act.ic.out;
    ./cfglp64 $file $2 $3 $4 $5 $6;
    mv $file.sym exp.sym.out;
    mv $file.spim exp.spim.out;
    mv $file.ic exp.ic.out;	
    diff -b -B act.sym.out exp.sym.out;
    diff -b -B act.spim.out exp.spim.out;
    diff -b -B act.ic.out exp.ic.out;
    rm -rf *.*.out ;
done

