#!/usr/bin/python

import sys, time, subprocess
import logging
import os.path
import hashlib
import watchdog
from watchdog.events import FileSystemEventHandler
from watchdog.observers import Observer

class Complier(object):
    """ execute `command` on the file with `dirname` as the base directory. """
    command = None
    args = ["-halt-on-error"]
    def __init__(self, full_path):
        self.full_path = full_path
        self.dirname = os.path.dirname(self.full_path)
        self.basename = os.path.basename(self.full_path)

    def execute(self):
        command = [self.command] + self.args + [self.basename]

        try:
            out = subprocess.check_output(command, universal_newlines=True, cwd=self.dirname)
        except subprocess.CalledProcessError as err:
            logging.error('processing error with {}'.format(command))
            #print(err)
            out = err.output
        print("\n\n")
        print(out.split('\n'))
        print("\n\n")
    


class FileWatcher(FileSystemEventHandler):
    hashes = {}
    def __init__(self, full_path, *args, **kwargs):
        self.full_path = full_path
        self.dirname = os.path.dirname(self.full_path)
        self.basename = os.path.basename(self.full_path)


        with open(self.full_path, mode='rb') as f:
            self.hashes[self.full_path] = hashlib.md5(f.read())

        super().__init__(*args, **kwargs)

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

            c = Complier(self.full_path)
            c.execute()


def watch_files(files):
    observer = Observer()
    for f in files.keys():
        f_dir, f_path = os.path.dirname(os.path.abspath(f)), os.path.abspath(f)
        logging.info("Monitoring '{}' in directory '{}'".format(f_path, f_dir))
        observer.schedule(FileWatcher(f_path), f_dir)
    observer.start()

    return observer


if __name__ == '__main__':
    import argparse
    logging.basicConfig(level=logging.INFO)

    parser = argparse.ArgumentParser(description='Watch and recompile .tex files when changed.')
    parser.add_argument('tex_files', metavar='TEX_FILES', type=str, nargs='+',
                        help='.tex files to watch')
    parser.add_argument('--engine', dest='engine',
                        default='xelatex',
                        help='tex engine to use (default: xelatex)')

    args = parser.parse_args()

    # find all files and dirs to watch
    tex_files = {}
    tex_dirs = []
    for i in args.tex_files:
        if os.path.isfile(i):
            tex_files[i] = True
        elif os.path.isdir(i):
            tex_dirs.append(i)
        else:
            logging.warn("Path '{}' is not a file or directory".format(i))


    Complier.command = args.engine
    # start a watch loop

    observer = watch_files(tex_files)
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        observer.stop()
    observer.join()


