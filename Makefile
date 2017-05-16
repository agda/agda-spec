default :
	make -C src

docs : default clean
	cp src/*.pdf docs/

.PHONY: clean
clean :
	mkdir -p docs/
	rm -f docs/*.pdf

# EOF
