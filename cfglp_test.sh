for file in `ls ./cfg/*.cfg`;
do
    echo "Diff for " $file ": "; 
    ./cfglp $file $1 $2 $3 -d > act.tmp.out;
    ./cfglp64 $file $1 $2 $3 -d > exp.tmp.out;
    diff -b -B act.tmp.out exp.tmp.out;
    rm -rf *.tmp.out;
done
