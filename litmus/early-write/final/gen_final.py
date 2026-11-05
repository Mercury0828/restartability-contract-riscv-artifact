# gen_final.py - final-memory tests of the early-write suite, with NO load of a or b anywhere.
# Reason: isla-axiomatic's last_write_to (isla-axiomatic/src/last_write_to.smt2) takes the co-maximal
# EVENT at the address without requiring it to be a write, so a load of a that reads 0 satisfies "*a = 0"
# (diag/DG_AN_fin_a0: hart 0 reloads 5, yet "*a = 0" is allowed). Removing every load of a and b
# removes the spurious witness. Source tests: ../dropped/*.toml (reader hart) and ../EW_BF_r575.toml.
import re, pathlib
here = pathlib.Path(__file__).parent
MARK = "0:x1 = 0x000000000000002A"

def strip_reader(src):
    # drop [thread.1] (the reader); renumber a [thread.2] (remote writer) to [thread.1]. Isla places
    # thread n's code at [threads] base + n * stride, so the reset pc moves with the number.
    src = re.sub(r'\[thread\.1\]\n.*?"""\n.*?"""\n\n', '', src, flags=re.S)
    return src.replace('[thread.2]', '[thread.1]').replace('"0x0000000080120000"', '"0x0000000080110000"')

def make(base_file, name, head, assertion, expect):
    src = (here.parent / base_file).read_text()
    src = strip_reader(src)
    lines = src.split('\n')
    # header: keep the program description, replace the first and last comment lines
    out = [f'# {name} - early-write suite, final memory (no load of a or b; see gen_final.py).']
    body = [l for l in lines[1:] if not l.startswith('# Tested') and not l.startswith('# Hart 1 reads')
            and not l.startswith('# In this pair')]
    src = '\n'.join(out + body)
    src = re.sub(r'^name = .*$', f'name = "{name}"', src, flags=re.M)
    src = re.sub(r'^expect = .*$', f'expect = "{expect}"', src, flags=re.M)
    src = re.sub(r'^assertion = .*$', f'assertion = "{assertion}"', src, flags=re.M)
    src = src.replace('# Hart 0 runs', f'# {head}\n# Hart 0 runs', 1)
    # the remote writer of the B pair is renumbered to hart 1, and the reader is gone
    src = re.sub(r'# Hart 2 writes 7 to lane 2,(.*)\n# fails\)\. Hart 1 reads .*\n',
                 r'# Hart 1 writes 7 to lane 2,\1\n# fails). Only lane 2 is written; there is no reader.\n', src)
    (here / f'{name}.toml').write_text(src, newline='\n')

A = [('fin56', '*a = 5 & *b = 6', 'sat'), ('fina0', '*a = 0', 'unsat'), ('finb0', '*b = 0', 'unsat')]
for tag, asn, exp in A:
    make(f'dropped/EW_AF_{tag}.toml', f'EW_AF_{tag}', f'Tested final memory: {asn}.',
         asn + (f' & {MARK}' if exp == 'sat' else ''), exp)
    make(f'dropped/EW_AN_{tag}.toml', f'EW_AN_{tag}', f'Tested final memory: {asn}.', asn, exp)
for v in (5, 7):
    make('EW_BF_r575.toml', f'EW_BF_fin{v}', f'Tested final memory: *a = {v}.', f'*a = {v} & {MARK}', 'sat')
    make('EW_BN_r575.toml', f'EW_BN_fin{v}', f'Tested final memory: *a = {v}.', f'*a = {v}', 'sat')
