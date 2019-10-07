#***************************** C and FORTRAN *************************** 
#                                              
#       Define C and Fortran compilers and compile options.
#

CFLAGS = -O -Wall -pthread
FFLAGS = -O -pthread

#
#	Set paths for C and Fortran compilers. 	
#

CF_PATH = /usr/bin/
CC =  ${CF_PATH}gcc ${CFLAGS}
F90 = ${CF_PATH}gfortran ${FFLAGS}

#
#*********************************************************************** 
#
#       The rest of the Makefile is independent of environment
#


HB = atest.o solver.o driver.o webgui.o

.f.o:
	${F90}  -c $< -o $@

.c.o:
	${CC}  -c $< -o $@

Hb: ${HB}
	${F90} ${HB}  -o Hb

${HB} : mg0.o

ATEST = atest.o solver.o driver.o

Atest: ${ATEST}
		${F90} ${ATEST} -o Atest

clean:
	rm -f *.o fort.* core* *.mod journl*.jnl* *.out jnltmp*.jnl* Hb*
