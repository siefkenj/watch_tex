# watch_tex.py
Monitor a LaTeX file for changes and recompile when it has changed

`watch_tex` is written in python and depends on the `watchdog` library to monitor files for changes.
`watchdog` can be installed with the command

	pip install watchdog

# watch_tex_gtk.py

`watch_tex_gtk.py` depends on the `watchdog` package as well as `pygobject` and `gtk+3`. Only one instance
of `watch_tex_gtk.py` will display. You may add files by draggin-and-dropping from nautilus or invoking directly on
the command line

	watch_tex_gtk.py <file name>

You may drag-and-drop multiple files at a time, but you may only add one file from the command line at a time.
