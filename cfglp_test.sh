for file in `ls ./cfg/*.cfg`;
do
    ./cfglp $file -tokens -d > act.tmp.out;
    ./cfglp64 $file -tokens -d > exp.tmp.out;
    diff act.tmp.out exp.tmp.out;
    rm -rf *.tmp.out;
done
