# makefile to compile MCPP version 2.7.1 and later for Visual C / nmake
#       2008/11 kmatsui
# You must first edit BINDIR, LIBDIR and INCDIR according to your system.
# To make compiler-independent-build of MCPP do:
#       nmake
# To make mcpp.lib (subroutine-build of mcpp) do:
#       nmake mcpplib
#       nmake mcpplib_install

NAME = mcpp

CC = cl
CFLAGS = $(CFLAGS) -Za -c -Zi
	# Add -Zi for debugging on Visual C / IDE
LINKFLAGS = -Fe$(NAME) -std=gnu++0x -Zi
CPPFLAGS = $(CPPFLAGS) -D_CRT_SECURE_NO_DEPRECATE # -Za
	# -D_CRT_SECURE_NO_DEPRECATE for Visual C 2005, 2008
	# -Za should not be specified for compiler-independent-built MCPP

!if "$(COMPILER)"=="MSC"
CPPFLAGS = $(CPPFLAGS) -DCOMPILER=MSC
!endif

OBJS = main.obj directive.obj eval.obj expand.obj support.obj system.obj \
        mbchar.obj

$(OBJS) : noconfig.H
main.obj directive.obj eval.obj expand.obj support.obj system.obj mbchar.obj: \
        system.H internal.H
.c.obj	:
	$(CC) $(CFLAGS) $(CPPFLAGS) $(MEM_MACRO) $<

clean	:
	-del *.obj *.i mcpp.H *.exe *.lib *.dll *.exp *.so

LIBDIR = "$_lib_dir_$"
INCDIR = "$_inc_dir_$"
CFLAGS = $(CFLAGS) -DMCPP_LIB

mcpplib: mcpplib_lib

# Debug mode: Do 'nmake DEBUG=1 ...'
!ifdef DEBUG
CFLAGS = $(CFLAGS) -MDd -D_DEBUG
LIBSUFFIX = d
!else
CFLAGS = $(CFLAGS) -O2 -MD -DNDEBUG
!endif

# UNICODE support: DO 'nmake UNICODE=1 ...'
!ifdef UNICODE
CFLAGS = $(CFLAGS) -DUNICODE -D_UNICODE
LIBSUFFIX = u$(LIBSUFFIX)
!endif

mcpplib_lib:	$(OBJS)
	lib -out:mcpp$(LIBSUFFIX).lib $(OBJS)

# DLL
DLL_VER = 0
SOBJS = main.so directive.so eval.so expand.so support.so system.so mbchar.so
.SUFFIXES: .so
.c.so	:
	$(CC) $(CFLAGS) $(CPPFLAGS) $(MEM_MACRO) -DDLL_EXPORT -TC -Fo$*.so $<
mcpplib_install:
	copy mcpp$(LIBSUFFIX).lib $(LIBDIR)
	copy mcpp_lib.h $(INCDIR)
	copy mcpp_out.h $(INCDIR)
	copy ..\inc\mcpp.h $(INCDIR)
mcpplib_uninstall:
	del $(LIBDIR)\mcpp$(LIBSUFFIX).lib
	del $(INCDIR)\mcpp*