#-------------------------------------------------------------------------
#
# Makefile--
#    Makefile for tcop
#
# IDENTIFICATION
#    src/backend/tcop/Makefile
#
#-------------------------------------------------------------------------

subdir = src/backend/tcop
top_builddir = ../../..
include $(top_builddir)/src/Makefile.global

OBJS = \
	cmdtag.o \
	dest.o \
	fastpath.o \
	fd_violation.o \
	postgres.o \
	pquery.o \
	utility.o

include $(top_srcdir)/src/backend/common.mk
