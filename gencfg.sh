for file in `ls test_files/*.c | awk -F"/" '{print $NF}'`;
do
	make -f Makefile.cfg FILE=$file;
done
