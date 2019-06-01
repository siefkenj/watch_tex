#!/usr/bin/python

from pprint import pprint
import signal, sys, os, subprocess, time
import threading, time
import urllib, urllib.parse
import pathlib
import gi
gi.require_version('Gtk', '3.0')
gi.require_version('Gdk', '3.0')
from gi.repository import Gtk, Gdk, GObject, GLib, Gio

import logging
import os.path
import hashlib
import collections, re

import curses
import watchdog
from watchdog.events import FileSystemEventHandler
from watchdog.observers import Observer



######################################################
######################################################
# Included here is MIT licensed code from  https://github.com/aclements/latexrun

# Copyright (c) 2013, 2014 Austin Clements

# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:

# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
class _Terminfo:
    def __init__(self):
        self.__tty = os.isatty(sys.stdout.fileno())
        if self.__tty:
            curses.setupterm()
        self.__ti = {}

    def __ensure(self, cap):
        if cap not in self.__ti:
            if not self.__tty:
                string = None
            else:
                string = curses.tigetstr(cap)
                if string is None or b'$<' in string:
                    # Don't have this capability or it has a pause
                    string = None
            self.__ti[cap] = string
        return self.__ti[cap]

    def has(self, *caps):
        return all(self.__ensure(cap) is not None for cap in caps)

    def send(self, *caps):
        # Flush TextIOWrapper to the binary IO buffer
        sys.stdout.flush()
        for cap in caps:
            # We should use curses.putp here, but it's broken in
            # Python3 because it writes directly to C's buffered
            # stdout and there's no way to flush that.
            if isinstance(cap, tuple):
                s = curses.tparm(self.__ensure(cap[0]), *cap[1:])
            else:
                s = self.__ensure(cap)
            sys.stdout.buffer.write(s)
terminfo = _Terminfo()

class Message(collections.namedtuple(
        'Message', 'typ filename lineno msg')):
    def emit(self):
        if self.filename:
            if self.filename.startswith('./'):
                finfo = self.filename[2:]
            else:
                finfo = self.filename
        else:
            finfo = '<no file>'
        if self.lineno is not None:
            finfo += ':' + str(self.lineno)
        finfo += ': '
        if self._color:
            terminfo.send('bold')
        sys.stdout.write(finfo)

        if self.typ != 'info':
            if self._color:
                terminfo.send(('setaf', 5 if self.typ == 'warning' else 1))
            sys.stdout.write(self.typ + ': ')
        if self._color:
            terminfo.send('sgr0')
        sys.stdout.write(self.msg + '\n')

    def as_tagged(self):
        """Returns the text of Message along with a list
        of tags and ranges for each tag about how the text should be highlighted"""
        base, line, typ, msg = "", "", "", ""
        
        if self.filename:
            if self.filename.startswith('./'):
                base = self.filename[2:]
            else:
                base = self.filename
        else:
            base = "<no file>"
        base += ":"

        if self.lineno:
            line = "{}:".format(self.lineno)

        typ = " {}: ".format(self.typ)

        msg = self.msg

        ret = ""
        tags = []
        for tag_name, string in (("base", base), ("line", line), ("type", typ), ("msg", msg)):
            if string:
                tags.append((tag_name, len(ret), len(ret) + len(string)))
                ret += string

        return ret, tags

    @classmethod
    def setup_color(cls, state):
        if state == 'never':
            cls._color = False
        elif state == 'always':
            cls._color = True
        elif state == 'auto':
            cls._color = terminfo.has('setaf', 'bold', 'sgr0')
        else:
            raise ValueError('Illegal color state {:r}'.format(state))

class LaTeXFilter:
    TRACE = False               # Set to enable detailed parse tracing

    def __init__(self, nowarns=[]):
        self.__data = ''
        self.__restart_pos = 0
        self.__restart_file_stack = []
        self.__restart_messages_len = 0
        self.__messages = []
        self.__first_file = None
        self.__fatal_error = False
        self.__missing_includes = False
        self.__pageno = 1
        self.__restart_pageno = 1

        self.__suppress = {cls: 0 for cls in nowarns}

    def feed(self, data, eof=False):
        """Feed LaTeX log data to the parser.
        The log data can be from LaTeX's standard output, or from the
        log file.  If there will be no more data, set eof to True.
        """

        self.__data += data
        self.__data_complete = eof

        # Reset to last known-good restart point
        self.__pos = self.__restart_pos
        self.__file_stack = self.__restart_file_stack.copy()
        self.__messages = self.__messages[:self.__restart_messages_len]
        self.__lstart = self.__lend = -1
        self.__pageno = self.__restart_pageno

        # Parse forward
        while self.__pos < len(self.__data):
            self.__noise()

        # Handle suppressed warnings
        if eof:
            msgs = ['%d %s warning%s' % (count, cls, "s" if count > 1 else "")
                    for cls, count in self.__suppress.items() if count]
            if msgs:
                self.__message('info', None,
                               '%s not shown (use -Wall to show them)' %
                               ', '.join(msgs), filename=self.__first_file)

        if eof and len(self.__file_stack) and not self.__fatal_error:
            # Fatal errors generally cause TeX to "succumb" without
            # closing the file stack, so don't complain in that case.
            self.__message('warning', None,
                           "unbalanced `(' in log; file names may be wrong")
        return self

    def get_messages(self):
        """Return a list of warning and error Messages."""
        return self.__messages

    def get_file_stack(self):
        """Return the file stack for the data that has been parsed.
        This results a list from outermost file to innermost file.
        The list may be empty.
        """

        return self.__file_stack

    def has_missing_includes(self):
        """Return True if the log reported missing \\include files."""
        return self.__missing_includes

    def __save_restart_point(self):
        """Save the current state as a known-good restart point.
        On the next call to feed, the parser will reset to this point.
        """
        self.__restart_pos = self.__pos
        self.__restart_file_stack = self.__file_stack.copy()
        self.__restart_messages_len = len(self.__messages)
        self.__restart_pageno = self.__pageno

    def __message(self, typ, lineno, msg, cls=None, filename=None):
        if cls is not None and cls in self.__suppress:
            self.__suppress[cls] += 1
            return
        filename = filename or (self.__file_stack[-1] if self.__file_stack
                                else self.__first_file)
        self.__messages.append(Message(typ, filename, lineno, msg))

    def __ensure_line(self):
        """Update lstart and lend."""
        if self.__lstart <= self.__pos < self.__lend:
            return
        self.__lstart = self.__data.rfind('\n', 0, self.__pos) + 1
        self.__lend = self.__data.find('\n', self.__pos) + 1
        if self.__lend == 0:
            self.__lend = len(self.__data)

    @property
    def __col(self):
        """The 0-based column number of __pos."""
        self.__ensure_line()
        return self.__pos - self.__lstart

    @property
    def __avail(self):
        return self.__pos < len(self.__data)

    def __lookingat(self, needle):
        return self.__data.startswith(needle, self.__pos)

    def __lookingatre(self, regexp, flags=0):
        return re.compile(regexp, flags=flags).match(self.__data, self.__pos)

    def __skip_line(self):
        self.__ensure_line()
        self.__pos = self.__lend

    def __consume_line(self, unwrap=False):
        self.__ensure_line()
        data = self.__data[self.__pos:self.__lend]
        self.__pos = self.__lend
        if unwrap:
            # TeX helpfully wraps all terminal output at 79 columns
            # (max_print_line).  If requested, unwrap it.  There's
            # simply no way to do this perfectly, since there could be
            # a line that happens to be 79 columns.
            #
            # We check for >=80 because a bug in LuaTeX causes it to
            # wrap at 80 columns instead of 79 (LuaTeX #900).
            while self.__lend - self.__lstart >= 80:
                if self.TRACE: print('<{}> wrapping'.format(self.__pos))
                self.__ensure_line()
                data = data[:-1] + self.__data[self.__pos:self.__lend]
                self.__pos = self.__lend
        return data

    # Parser productions

    def __noise(self):
        # Most of TeX's output is line noise that combines error
        # messages, warnings, file names, user errors and warnings,
        # and echos of token lists and other input.  This attempts to
        # tease these apart, paying particular attention to all of the
        # places where TeX echos input so that parens in the input do
        # not confuse the file name scanner.  There are three
        # functions in TeX that echo input: show_token_list (used by
        # runaway and show_context, which is used by print_err),
        # short_display (used by overfull/etc h/vbox), and show_print
        # (used in issue_message and the same places as
        # show_token_list).
        lookingat, lookingatre = self.__lookingat, self.__lookingatre
        if self.__col == 0:
            # The following messages are always preceded by a newline
            if lookingat('! '):
                return self.__errmessage()
            # xelatex does not prefix this error with !.
            if lookingat('No pages of output.'):
                self.__consume_line()
                return self.__message('error', None, 'No pages of output.')
            if lookingat('!pdfTeX error: '):
                return self.__pdftex_fail()
            if lookingat('Runaway '):
                return self.__runaway()
            if lookingatre(r'(Overfull|Underfull|Loose|Tight) \\[hv]box \('):
                return self.__bad_box()
            if lookingatre('(Package |Class |LaTeX |pdfTeX )?(\w+ )?warning: ', re.I):
                return self.__generic_warning()
            if lookingatre('No file .*\\.tex\\.$', re.M):
                # This happens with \includes of missing files.  For
                # whatever reason, LaTeX doesn't consider this even
                # worth a warning, but I do!
                self.__message('warning', None,
                               self.__simplify_message(
                                   self.__consume_line(unwrap=True).strip()))
                self.__missing_includes = True
                return
            # Other things that are common and irrelevant
            if lookingatre(r'(Package|Class|LaTeX) (\w+ )?info: ', re.I):
                return self.__generic_info()
            if lookingatre(r'(Document Class|File|Package): '):
                # Output from "\ProvidesX"
                return self.__consume_line(unwrap=True)
            if lookingatre(r'\\\w+=\\[a-z]+\d+\n'):
                # Output from "\new{count,dimen,skip,...}"
                return self.__consume_line(unwrap=True)

        # print(self.__data[self.__lstart:self.__lend].rstrip())
        # self.__pos = self.__lend
        # return

        # Now that we've substantially reduced the spew and hopefully
        # eliminated all input echoing, we're left with the file name
        # stack, page outs, and random other messages from both TeX
        # and various packages.  We'll assume at this point that all
        # parentheses belong to the file name stack or, if they're in
        # random other messages, they're at least balanced and nothing
        # interesting happens between them.  For page outs, ship_out
        # prints a space if not at the beginning of a line, then a
        # "[", then the page number being shipped out (this is
        # usually, but not always, followed by "]").
        m = re.compile(r'[(){}\n]|(?<=[\n ])\[\d+', re.M).\
            search(self.__data, self.__pos)
        if m is None:
            self.__pos = len(self.__data)
            return
        self.__pos = m.start() + 1
        ch = self.__data[m.start()]
        if ch == '\n':
            # Save this as a known-good restart point for incremental
            # parsing, since we definitely didn't match any of the
            # known message types above.
            self.__save_restart_point()
        elif ch == '[':
            # This is printed at the end of a page, so we're beginning
            # page n+1.
            self.__pageno = int(self.__lookingatre(r'\d+').group(0)) + 1
        elif ((self.__data.startswith('`', m.start() - 1) or
               self.__data.startswith('`\\', m.start() - 2)) and
               self.__data.startswith('\'', m.start() + 1)):
            # (, ), {, and } sometimes appear in TeX's error
            # descriptions, but they're always in `'s (and sometimes
            # backslashed)
            return
        elif ch == '(':
            # XXX Check that the stack doesn't drop to empty and then re-grow
            first = self.__first_file is None and self.__col == 1
            filename = self.__filename()
            self.__file_stack.append(filename)
            if first:
                self.__first_file = filename
            if self.TRACE:
                print('<{}>{}enter {}'.format(
                    m.start(), ' '*len(self.__file_stack), filename))
        elif ch == ')':
            if len(self.__file_stack):
                if self.TRACE:
                    print('<{}>{}exit {}'.format(
                        m.start(), ' '*len(self.__file_stack),
                        self.__file_stack[-1]))
                self.__file_stack.pop()
            else:
                self.__message('warning', None,
                               "extra `)' in log; file names may be wrong ")
        elif ch == '{':
            # TeX uses this for various things we want to ignore, like
            # file names and print_mark.  Consume up to the '}'
            epos = self.__data.find('}', self.__pos)
            if epos != -1:
                self.__pos = epos + 1
            else:
                self.__message('warning', None,
                               "unbalanced `{' in log; file names may be wrong")
        elif ch == '}':
            self.__message('warning', None,
                           "extra `}' in log; file names may be wrong")

    def __filename(self):
        initcol = self.__col
        first = True
        name = ''
        # File names may wrap, but if they do, TeX will always print a
        # newline before the open paren
        while first or (initcol == 1 and self.__lookingat('\n')
                        and self.__col >= 79):
            if not first:
                self.__pos += 1
            m = self.__lookingatre(r'[^(){} \n]*')
            name += m.group()
            self.__pos = m.end()
            first = False
        return name

    def __simplify_message(self, msg):
        msg = re.sub(r'^(?:Package |Class |LaTeX |pdfTeX )?([^ ]+) (?:Error|Warning): ',
                     r'[\1] ', msg, flags=re.I)
        msg = re.sub(r'\.$', '', msg)
        msg = re.sub(r'has occurred (while \\output is active)', r'\1', msg)
        return msg

    def __errmessage(self):
        # Procedure print_err (including \errmessage, itself used by
        # LaTeX's \GenericError and all of its callers), as well as
        # fatal_error.  Prints "\n!  " followed by error text
        # ("Emergency stop" in the case of fatal_error).  print_err is
        # always followed by a call to error, which prints a period,
        # and a newline...
        msg = self.__consume_line(unwrap=True)[1:].strip()
        is_fatal_error = (msg == 'Emergency stop.')
        msg = self.__simplify_message(msg)
        # ... and then calls show_context, which prints the input
        # stack as pairs of lines giving the context.  These context
        # lines are truncated so they never wrap.  Each pair of lines
        # will start with either "<something> " if the context is a
        # token list, "<*> " for terminal input (or command line),
        # "<read ...>" for stream reads, something like "\macroname
        # #1->" for macros (though everything after \macroname is
        # subject to being elided as "..."), or "l.[0-9]+ " if it's a
        # file.  This is followed by the errant input with a line
        # break where the error occurred.
        lineno = None
        found_context = False
        stack = []
        while self.__avail:
            m1 = self.__lookingatre(r'<([a-z ]+|\*|read [^ >]*)> |\\.*(->|...)')
            m2 = self.__lookingatre('l\.[0-9]+ ')
            if m1:
                found_context = True
                pre = self.__consume_line().rstrip('\n')
                stack.append(pre)
            elif m2:
                found_context = True
                pre = self.__consume_line().rstrip('\n')
                info, rest = pre.split(' ', 1)
                lineno = int(info[2:])
                stack.append(rest)
            elif found_context:
                # Done with context
                break
            if found_context:
                # Consume the second context line
                post = self.__consume_line().rstrip('\n')
                # Clean up goofy trailing ^^M TeX sometimes includes
                post = re.sub(r'\^\^M$', '', post)
                if post[:len(pre)].isspace() and not post.isspace():
                    stack.append(len(stack[-1]))
                    stack[-2] += post[len(pre):]
            else:
                # If we haven't found the context, skip the line.
                self.__skip_line()
        stack_msg = ''
        for i, trace in enumerate(stack):
            stack_msg += ('\n         ' + (' ' * trace) + '^'
                          if isinstance(trace, int) else
                          '\n      at ' + trace.rstrip() if i == 0 else
                          '\n    from ' + trace.rstrip())

        if is_fatal_error:
            # fatal_error always prints one additional line of message
            info = self.__consume_line().strip()
            if info.startswith('*** '):
                info = info[4:]
            msg += ': '  + info.lstrip('(').rstrip(')')

        self.__message('error', lineno, msg + stack_msg)
        self.__fatal_error = True

    def __pdftex_fail(self):
        # Procedure pdftex_fail.  Prints "\n!pdfTeX error: ", the
        # message, and a newline.  Unlike print_err, there's never
        # context.
        msg = self.__consume_line(unwrap=True)[1:].strip()
        msg = self.__simplify_message(msg)
        self.__message('error', None, msg)

    def __runaway(self):
        # Procedure runaway.  Prints "\nRunaway ...\n" possibly
        # followed by token list (user text).  Always followed by a
        # call to print_err, so skip lines until we see the print_err.
        self.__skip_line()      # Skip "Runaway ...\n"
        if not self.__lookingat('! ') and self.__avail:
            # Skip token list, which is limited to one line
            self.__skip_line()

    def __bad_box(self):
        # Function hpack and vpack.  hpack prints a warning, a
        # newline, then a short_display of the offending text.
        # Unfortunately, there's nothing indicating the end of the
        # offending text, but it should be on one (possible wrapped)
        # line.  vpack prints a warning and then, *unless output is
        # active*, a newline.  The missing newline is probably a bug,
        # but it sure makes our lives harder.
        origpos = self.__pos
        msg = self.__consume_line()
        m = re.search(r' in (?:paragraph|alignment) at lines ([0-9]+)--([0-9]+)', msg) or \
            re.search(r' detected at line ([0-9]+)', msg)
        if m:
            # Sometimes TeX prints crazy line ranges like "at lines
            # 8500--250".  The lower number seems roughly sane, so use
            # that.  I'm not sure what causes this, but it may be
            # related to shipout routines messing up line registers.
            lineno = min(int(m.group(1)), int(m.groups()[-1]))
            msg = msg[:m.start()]
        else:
            m = re.search(r' while \\output is active', msg)
            if m:
                lineno = None
                msg = msg[:m.end()]
            else:
                self.__message('warning', None,
                               'malformed bad box message in log')
                return
        # Back up to the end of the known message text
        self.__pos = origpos + m.end()
        if self.__lookingat('\n'):
            # We have a newline, so consume it and look for the
            # offending text.
            self.__pos += 1
            # If there is offending text, it will start with a font
            # name, which will start with a \.
            if 'hbox' in msg and self.__lookingat('\\'):
                self.__consume_line(unwrap=True)
        msg = self.__simplify_message(msg) + ' (page {})'.format(self.__pageno)
        cls = msg.split(None, 1)[0].lower()
        self.__message('warning', lineno, msg, cls=cls)

    def __generic_warning(self):
        # Warnings produced by LaTeX's \GenericWarning (which is
        # called by \{Package,Class}Warning and \@latex@warning),
        # warnings produced by pdftex_warn, and other random warnings.
        msg, cls = self.__generic_info()
        # Most warnings include an input line emitted by \on@line
        m = re.search(' on input line ([0-9]+)', msg)
        if m:
            lineno = int(m.group(1))
            msg = msg[:m.start()]
        else:
            lineno = None
        msg = self.__simplify_message(msg)
        self.__message('warning', lineno, msg, cls=cls)

    def __generic_info(self):
        # Messages produced by LaTeX's \Generic{Error,Warning,Info}
        # and things that look like them
        msg = self.__consume_line(unwrap=True).strip()
        # Package and class messages are continued with lines
        # containing '(package name)            '
        pkg_name = msg.split(' ', 2)[1]
        prefix = '(' + pkg_name + ')            '
        while self.__lookingat(prefix):
            # Collect extra lines.  It's important that we keep these
            # because they may contain context information like line
            # numbers.
            extra = self.__consume_line(unwrap=True)
            msg += ' ' + extra[len(prefix):].strip()
        return msg, pkg_name.lower()

######################################################
######################################################



class WatchedFileList:
    """Stores a bunch of WatchedFile objects."""

    def __init__(self):
        self.list = {}

    def append(self, watched_file):
        if not isinstance(watched_file, WatchedFile):
            # we passed in a string. Create an appropriate object
            watched_file = WatchedFile(full_path=watched_file)
        self.list[str(watched_file)] = watched_file

        # we cannot do watched_file.on_change = self.on_change
        # because we need self.on_change to be dynamically looked
        # up. Otherwise, when it is overridden, there wouldn't be
        # an effect.
        watched_file.on_change = lambda *x: self.on_change(*x)

        watched_file.watch()
        return str(watched_file), watched_file

    def get(self, key):
        if key in self.list:
            return self.list[key]
        return None

    def remove(self, key):
        del self.list[key]

    def on_change(self, *args):
        pass

    def __iter__(self):
        return self.list.items().__iter__()

class WatchedFile:
    on_change = lambda *x: None
    
    def __init__(self, full_path=None, basename=None, dirname=None):
        self.parsed = None
        self.basename = basename
        self.dirname = dirname
        if full_path:
            parsed = parse_filenames(full_path)[0]
            self.parsed = parsed
            self.basename = parsed['file']
            self.dirname = parsed['dir']
        if not self.parsed:
            self.parsed = parse_filenames("{}/{}".format(self.dirname, self.basename))[0]
        self.file_watcher = None
        self.observer = None
        self.status = "Unchanged"
        self.latex_messages = []
        self.last_duration = 1
        self.last_compile_start = 0
        self.last_compile_end = 1
        self.estimated_complete = 0

        # if there is a symbolic link to a file, or the file uses
        # an \input, we want to watch the base files or the \input
        # files, but trigger a rebuild on the parent.
        self.child_watchers = []
        self.child_watched_filenames = []

        # symlinks don't trigger changes, so watch the parent
        if pathlib.Path(self.full_path).is_symlink():
            self.child_watched_filenames.append(str(pathlib.Path(self.full_path).resolve()))

        # check for any \input commands and watch the files they reference
        with open(self.full_path) as f:
            for l in f.readlines():
                matches = re.findall(r"^\s*\\input{([^}]*)}", l)
                if matches:
                    path = pathlib.Path("{}/{}".format(self.dirname, matches[0])).resolve()
                    print("yy",path, path.is_file())
                    if not path.is_file():
                        # if path isn't a file, maybe it doesn't have the ".tex"
                        if path.with_suffix(".tex").is_file():
                            path = path.with_suffix(".tex")
                        else:
                            continue
                    self.child_watched_filenames.append(str(path))



    
    def __repr__(self):
        return "WatchedFile(None, '{}', '{}')".format(self.basename, self.dirname)

    @property
    def full_path(self):
        return "{}/{}".format(self.dirname, self.basename)

    def watch(self):
        print("Watching", self)
        if not self.parsed['is_file']:
            print("Cannot watch", self, ", not a file.")
            return

        self.file_watcher = FileWatcher(self.full_path)
        self.file_watcher.change_callback = self._on_change
        
        self.observer = Observer()
        self.observer.schedule(self.file_watcher, self.dirname)
        self.observer.start()

        for path in self.child_watched_filenames:
            self._watch_child(path)

    def _watch_child(self, path):
        """Watch `path`, but when `path` changes, trigger a recompile
        of `self`. This used for watching symbolic links of `\import` """
        print("Watching child", path)
        parsed = parse_filenames(path)[0]
        if not parsed['is_file']:
            print("Cannot watch", path, ", not a file.")
            return

        file_watcher = FileWatcher(path)
        file_watcher.change_callback = self._on_change
        
        observer = Observer()
        observer.schedule(file_watcher, str(pathlib.Path(path).parent))
        observer.start()

        self.child_watchers.append(observer)


    def unwatch(self):
        print("Unwatching", self)
        self.observer.stop()

        for observer in self.child_watchers:
            observer.stop()

    def as_list_store_row(self):
        return (str(self), self.status, self.estimated_complete, self.basename)

    def trigger(self):
        """Triggers a recompile"""
        self._on_change()

    def _on_change(self, *args):
        """Runs when file is changed. self.on_change is called after
        this method. self.on_change is also called whenever this
        file has a status update"""

        def compile_thread():
            def progress_updater():
                self.estimated_complete = 0
                while self.status == "Compiling..." and self.estimated_complete < 100:
                    elapsed = time.time() - self.last_compile_start
                    self.estimated_complete = min(int(100 * elapsed / self.last_duration), 100)
                    self.on_change(*args)
                    time.sleep(.1)
            # start a thread to update the progress while compiling
            thread = threading.Thread(target=progress_updater)
            thread.daemon = True
            

            # update everything before compiling
            self.status = "Compiling..."
            self.on_change(*args)

            # compile
            self.last_compile_start = time.time()
            thread.start()
            
            c = Complier(self.full_path)
            self.latex_messages = c.execute()

            self.last_compile_end = time.time()
            self.last_duration = self.last_compile_end - self.last_compile_start

            self.status = "Compiled"
            self.estimated_complete = 100
            if any(x.typ == "error" for x in self.latex_messages):
                self.status = "Error"
                self.estimated_complete = 0
            self.on_change(*args)

        thread = threading.Thread(target=compile_thread)
        thread.daemon = True
        thread.start()

class FileWatcher(FileSystemEventHandler):
    """Class needed by watchdog to monitor files"""
    hashes = {}
    change_callback = lambda *x: None

    def __init__(self, full_path, *args, **kwargs):
        self.full_path = full_path
        self.dirname = os.path.dirname(self.full_path)
        self.basename = os.path.basename(self.full_path)

        with open(self.full_path, mode='rb') as f:
            self.hashes[self.full_path] = hashlib.md5(f.read())

        super().__init__(*args, **kwargs)

    def on_moved(self, event):
        # some editors move a file instead of editing a file;
        # treat these events `moved` as `modified` events
        if isinstance(event, watchdog.events.FileMovedEvent):
            ev = watchdog.events.FileModifiedEvent(event.dest_path)
            self.on_modified(ev)

    def on_modified(self, event):
        if os.path.abspath(event.src_path) != os.path.abspath(self.full_path):
            return
        with open(self.full_path, mode='rb') as f:
            f_hash = hashlib.md5(f.read()).hexdigest()
            if f_hash == self.hashes[self.full_path]:
                # the hash didn't change, so don't do anything
                return
            self.hashes[self.full_path] = f_hash
            logging.info('File changed \'{}\' with hash {}'.format(self.full_path, f_hash))
            
            self.change_callback(self)








class Complier(object):
    """ execute `command` on the file with `dirname` as the base directory. """
    command = "lualatex"
    args = ["-halt-on-error"]
    def __init__(self, full_path):
        self.full_path = full_path
        self.dirname = os.path.dirname(self.full_path)
        self.basename = os.path.basename(self.full_path)

    def execute(self):

        command = [self.command] + self.args + [self.basename]
        
        print("executing", command)

        try:
            out = subprocess.check_output(command, universal_newlines=True, cwd=self.dirname)
        except subprocess.CalledProcessError as err:
            logging.error('processing error with {}'.format(command))
            #print(err)
            out = err.output

        # parse the output and only show the important bits
        print("\n")
        lf = LaTeXFilter()
        lf.feed(out)
        for m in lf.get_messages():
            m.emit()

        return lf.get_messages() or []



def parse_filenames(text):
    """Parse `text` assuming it is a newline or linefeed-newline
    separated list containing file names."""
    ret = []
    for f in text.split("\n"):
        f = f.strip()
        parsed = urllib.parse.urlparse(f)
        fname = urllib.parse.unquote(parsed.path)
        if fname:
            path = pathlib.Path(fname)
            file_name = str(path.relative_to(path.parent))
            dir_name = str(path.parent)
            if path.is_dir():
                file_name = ''
                dir_name = str(path)
            ret.append({
                'file': file_name,
                'dir': dir_name,
                'is_file': path.is_file(),
                'is_dir': path.is_dir()
                })
    return ret


class WatchTexApplication(Gtk.Application):
    __gtype_name__ = "WatchTexApplication"

    def __init__(self):
        super().__init__(application_id='x.x.WatchTex', flags=Gio.ApplicationFlags.HANDLES_COMMAND_LINE)
        
        if hasattr(self.props, 'register_session'):
            self.props.register_session = True

        self.window = None
        self.watched_file_list = WatchedFileList()

    def do_command_line(self, command_line):
        argv = command_line.get_arguments()
        cwd = command_line.get_cwd()
        print("From commandline got", argv, cwd)
        
        # add the file to the watching queue if one was specified
        if len(argv) > 1:
            self.watched_file_list.append("{}/{}".format(cwd, argv[-1]))
        
        self.do_activate()
        return 0

    def do_activate(self):
        if not self.window:
            self.window = WatchTexWindow(self, self.watched_file_list)

        print("Application Activating")
        self.window.sync_list()
        self.window.present()

    def do_startup(self):
        Gtk.Application.do_startup(self)
        # allow ctrl+C to quit the app
        signal.signal(signal.SIGINT, signal.SIG_DFL)

    def do_shutdown(self):
        Gtk.Application.do_shutdown(self)
        if self.window:
            self.window.destroy()

class WatchTexWindow(Gtk.ApplicationWindow):
    __gtype_name__ = "WatchTexWindow"

    def __init__(self, app, watched_file_list):
        super().__init__(application=app)
        self.app = app
        self.watched_file_list = watched_file_list
        self.watched_file_list.on_change = self.async_update

        self.builder = Gtk.Builder()
        self.builder.add_from_file("ui.glade")

        # stuff the contents of main_window into self
        main_window = self.builder.get_object("main_window")
        box = main_window.get_child()
        main_window.remove(box)
        self.add(box)
        self.props.default_width = main_window.props.default_width
        self.props.default_height = main_window.props.default_height

        self.files_queue = self.builder.get_object("files_queue")
        self.popover = self.builder.get_object("popover")
        self.treeview = self.builder.get_object("treeview1")
        self.textbuffer = self.builder.get_object("textbuffer")
        self.tags = {}
        for tag_name in ("base", "type", "line", "msg"):
            self.tags[tag_name] = self.builder.get_object(tag_name)

        self.textbuffer.set_text("hi there\n this is really cool\ntext!!")

        self.treeview.drag_dest_set(Gtk.DestDefaults.ALL, [], Gdk.DragAction.COPY)
        self.treeview.drag_dest_set_target_list(None)
        self.treeview.drag_dest_add_text_targets()
        
        self.builder.connect_signals(self)
    
    def on_tree_button_press(self, treeview, button):
        path_info = treeview.get_path_at_pos(button.x, button.y)
        if path_info:
            path, col, cellx, celly = path_info
            treeview.grab_focus()
            treeview.set_cursor(path, col, 0)
            
            if button.button == 3:
                rect = treeview.get_cell_area(path, col)
                rect.y = rect.y + rect.height
                self.popover.set_pointing_to(rect)
                self.popover.show_all()
                self.popover.popup()
            print(path, hash(self.files_queue[path].iter), self.files_queue[path])

    def on_tree_drop(self, treeview, drag_context, x, y, data, *rest):
        print("Data dragged and dropped")
        text = data.get_text()
        paths = parse_filenames(text)
        for p in paths:
            if p['is_file']:
                self.watched_file_list.append("{}/{}".format(p['dir'], p['file']))
        self.sync_list()

    def sync_list(self):
        """Make sure whatever is in `self.watched_file_list` is also in the treeview"""

        existing_hashes = set()

        # grab the current selection since we need to update more for currently selected things
        tree_model, tree_iter = self.treeview.get_selection().get_selected()
        current_selection = None
        if tree_iter:
            current_selection = tree_model[tree_iter][0]

        for i,row in enumerate(tuple(self.files_queue)):
            h, *_ = row
            existing_hashes.add(h)
            something_changed = False

            item = self.watched_file_list.get(h)
            if item:
                new_row = item.as_list_store_row()
                for j,val in enumerate(row):
                    if val != new_row[j]:
                        row[j] = new_row[j]
                        something_changed = True
            else:
                # this is an item that isn't in the list store
                pass
            if item and h == current_selection and something_changed:
                # if something changed with the current selection, update it
                # right away
                self.update_current_selection()
            
        for h,item in self.watched_file_list:
            if h not in existing_hashes:
                self.files_queue.append(item.as_list_store_row())

    def update_current_selection(self, *args):
        tree_model, tree_iter = self.treeview.get_selection().get_selected()
        if not tree_iter:
            # if there is nothing currently selected, do nothing
            self.current_selection = None
            print("Warning, nothing selected...")
            return
        current_selection = tree_model[tree_iter][0]
        self.current_selection = current_selection

        data = self.watched_file_list.get(current_selection)
        if not data:
            print("Warning, can't find data for updating", current_selection)
            self.textbuffer.set_text("")
            return

        lines = [x.as_tagged() for x in data.latex_messages]
        # setting the text with set_text will destroy existing tags, so 
        # we need to set the text first, then insert all the tags
        full_text = "\n".join(x[0] for x in lines)
        self.textbuffer.set_text(full_text)
        curr = 0
        for line, tags in lines:
            for tag_name, start, end in tags:
                iter_start = self.textbuffer.get_iter_at_offset(start + curr)
                iter_end = self.textbuffer.get_iter_at_offset(end + curr)
                self.textbuffer.apply_tag(self.tags[tag_name], iter_start, iter_end)
            curr += len(line)
            # lines are joined with a newline so offset one extra
            curr += 1

    def on_button_trigger_recompile(self, *args):
        if not self.current_selection:
            return
        watched = self.watched_file_list.get(self.current_selection)
        if not watched:
            return
        watched.trigger()

    def on_open_pdf_clicked(self, *args):
        if not self.current_selection:
            return
        watched = self.watched_file_list.get(self.current_selection)
        if not watched:
            return
        pdf_filename = "{}/{}.pdf".format(watched.dirname, watched.basename[:-4])
        path = pathlib.Path(pdf_filename)
        if path.is_file():
            Gtk.show_uri(Gdk.Screen.get_default(), "file://{}".format(pdf_filename), 1)
        else:
            print("Cannot find PDF file", pdf_filename)

    def on_open_tex_clicked(self, *args):
        if not self.current_selection:
            return
        watched = self.watched_file_list.get(self.current_selection)
        if not watched:
            return
        filename = "{}/{}".format(watched.dirname, watched.basename)
        path = pathlib.Path(filename)
        if path.is_file():
            Gtk.show_uri(Gdk.Screen.get_default(), "file://{}".format(filename), 1)
        else:
            print("Cannot find TEX file", filename)

    def on_unwatch_clicked(self, *args):
        if not self.current_selection:
            return
        watched = self.watched_file_list.get(self.current_selection)
        if not watched:
            return

        watched.unwatch()
        self.watched_file_list.remove(self.current_selection)
        # find the index of what we've unwatched
        for i,row in enumerate(tuple(self.files_queue)):
            h, *_ = row
            if h == self.current_selection:
                break
        del self.files_queue[i]
        self.sync_list()
        
        
    def async_update(self, *args):
        GLib.idle_add(self.sync_list)



def main(version=''):
    app = WatchTexApplication()
    exit_status = app.run(sys.argv)
    sys.exit(exit_status)


if __name__ == '__main__':
    Message.setup_color('auto')
    main()
sys.exit()
