mymalloc.so : 
	          gcc -o microalloc.so -fPIC -shared -Og -g3 -ldl -Wall mm.c

clean : 
	    rm microalloc.so
