"""Pure-Python regression for PuTTY's absolute remote destinations; no Lean."""
from gcp_cfr import VM, scp_destination, submission_guard


def main():
    run = 'cfr-baseline-20261028T211424Z-5ddb91'
    assert scp_destination('/home/dfredriksen_quantyra_org', run) == (
        VM + ':/home/dfredriksen_quantyra_org/quantyra-cfr-runs/' + run + '/')
    for invalid in ['~', '/home/../x', '/home/x;echo', 'relative']:
        try:
            scp_destination(invalid, run)
        except ValueError:
            continue
        raise AssertionError('Accepted invalid remote home: ' + invalid)
    script = submission_guard(run)
    checks = ['pgrep -x lean', 'test -x', 'flock -n', 'test ! -e "$run"', 'mkdir "$run"', 'CFR_HOME=', 'CFR_CACHE=']
    assert [script.index(s) for s in checks] == sorted(script.index(s) for s in checks)
    assert 'nohup' not in script and 'lake build' not in script
    try:
        submission_guard('cfr-x;touch-bad')
    except ValueError:
        pass
    else:
        raise AssertionError('Accepted shell metacharacter in run identity')
    print('PASS: absolute destinations, invalid-home/run controls, ordered non-compiling guard')


if __name__ == '__main__':
    main()
