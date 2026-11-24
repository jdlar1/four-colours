from pathlib import Path
base=Path.cwd()
def records(path):return path.read_text().strip().split('\n\n')
def write(path,rows):path.write_text('\n\n'.join(rows)+'\n\n')
