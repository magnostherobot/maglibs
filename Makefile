TRGT = libarray.so

default : all

all : $(TRGT)

lib%.so : %.c
	$(CC) -shared -o $@ $^

clean :
	$(RM) *.idr~ $(TRGT) *.o *.s *.ll *.bc -r build/
