#!/usr/bin/env python3
import argparse
import os
import shutil
import subprocess
import sys
import tempfile

def parse_args():
    ap = argparse.ArgumentParser()
    ap.add_argument('player', metavar='PLAYER',
            help='path to the SCALE Player.x binary')
    ap.add_argument('program', metavar='PROGRAM',
            help='bytecode file to run')
    return ap.parse_args()

def start_player(args, i, prog_dir, show_output=False):
    # Use abspath since we're going to chdir before running the program
    cmd = (os.path.abspath(args.player), str(i), os.path.abspath(prog_dir))
    dest = None if show_output else subprocess.DEVNULL
    cwd = os.path.dirname(args.player)
    return subprocess.Popen(cmd, stdout=dest, stderr=dest, cwd=cwd)

def main():
    args = parse_args()

    prog_name = os.path.splitext(os.path.basename(args.program))[0]

    with tempfile.TemporaryDirectory() as temp_dir:
        prog_dir = os.path.join(temp_dir, prog_name)
        prog_bc = os.path.join(prog_dir, prog_name + '-0.bc')
        prog_sch = os.path.join(prog_dir, prog_name + '.sch')

        os.mkdir(prog_dir)
        shutil.copy(args.program, prog_bc)
        with open(os.path.join(prog_sch), 'w') as f:
            f.write('1\n')
            f.write('1\n')
            f.write('%s-0\n' % prog_name)
            f.write('1 0\n')
            f.write('0\n')
            f.write('[cheesecloth compiler]\n')

        p0 = start_player(args, 0, prog_dir, show_output=True)
        p1 = start_player(args, 1, prog_dir)
        p2 = start_player(args, 2, prog_dir)

        p0.wait()
        p1.wait()
        p2.wait()

if __name__ == '__main__':
    main()

