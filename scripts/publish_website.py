#!/usr/bin/env python3
"""Build, check and publish the complete site to the gh-pages delivery branch.

Run from a clean source checkout after generating the API. The branch's Pages
workflow deploys its static output. Work happens in a temporary clone, leaving
the source checkout's branch and index untouched. No Lean build is performed.
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def git(*args, cwd=ROOT):
    return subprocess.check_output(['git', *args], cwd=cwd, text=True).strip()


def main():
    if git('status', '--porcelain'):
        raise SystemExit('Commit source changes before publishing the website.')
    source = git('rev-parse', 'HEAD')
    # Public source links must resolve to a commit already on the remote.
    remote_main = git('ls-remote', 'origin', 'refs/heads/main').split()[0]
    if source != remote_main:
        raise SystemExit('Push this source commit to origin/main before publishing.')
    subprocess.run([sys.executable, 'scripts/build_website.py'], cwd=ROOT, check=True)
    subprocess.run([sys.executable, 'scripts/check_website.py'], cwd=ROOT, check=True)
    site = ROOT / '_site'
    state = json.loads((site / 'build.json').read_text())
    if state['dirty'] or state['commit'] != source or not state['api_generated']:
        raise SystemExit('A clean, current website with the complete API is required.')
    if any(p.is_symlink() for p in site.rglob('*')):
        raise SystemExit('Pages artifacts cannot contain symbolic links.')
    remote = git('remote', 'get-url', 'origin')
    exists = bool(git('ls-remote', '--heads', 'origin', 'gh-pages'))
    with tempfile.TemporaryDirectory(prefix='multiplicative-bases-pages-') as temporary:
        target = Path(temporary) / 'delivery'
        if exists:
            subprocess.run(['git', 'clone', '--depth', '1', '--single-branch',
                            '--branch', 'gh-pages', remote, str(target)], check=True)
        else:
            target.mkdir()
            git('init', '--initial-branch=gh-pages', cwd=target)
            git('remote', 'add', 'origin', remote, cwd=target)
        git('config', 'user.name', git('config', 'user.name'), cwd=target)
        git('config', 'user.email', git('config', 'user.email'), cwd=target)
        if (target / '_site').exists():
            shutil.rmtree(target / '_site')
        shutil.copytree(site, target / '_site')
        workflow = target / '.github/workflows/pages.yml'
        workflow.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / '.github/workflows/pages.yml', workflow)
        git('add', '--', '_site', '.github/workflows/pages.yml', cwd=target)
        if not git('diff', '--cached', '--name-only', cwd=target):
            print('The published branch already contains this website.')
            return
        git('commit', '-m', f'Publish website from {source}', cwd=target)
        # A normal fast-forward push detects a concurrent publication.
        subprocess.run(['git', 'push', 'origin', 'HEAD:refs/heads/gh-pages'],
                       cwd=target, check=True)
        print('Published site branch:', git('rev-parse', 'HEAD', cwd=target))
    print('Deployment: https://github.com/haruhisa-enomoto/multiplicative-bases-deformations/actions/workflows/pages.yml')


if __name__ == '__main__':
    main()
