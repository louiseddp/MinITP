all:
	make -C src && \
	cp -f src/proplog .

clean:
	make -C src clean && \
	rm -f proplog
