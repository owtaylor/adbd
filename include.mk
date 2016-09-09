top_builddir ?= $(top_srcdir)
-include $(top_builddir)/config.mk

prefix ?= /usr
exec_prefix ?= $(prefix)
bindir ?= $(prefix)/bin
sbindir ?= $(exec_prefix)/sbin
datadir ?= $(prefix)/share
mandir ?= $(datadir)/man
sysconfdir ?= $(prefix)/etc
OPT_CFLAGS ?= -O2 -g
OPT_CXXFLAGS ?= -O2 -g

PROPERTIES_PATH=$(sysconfdir)/adb.properties
