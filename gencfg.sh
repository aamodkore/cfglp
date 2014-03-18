for file in `ls test_files/*.c | awk -F"/" '{print $NF}'`;
do
	make -f Makefile.cfg FILE=$file;
done

mkdir -p cfg

for file in `ls test_files/*.cfg`;
do
	mv $file cfg
done
