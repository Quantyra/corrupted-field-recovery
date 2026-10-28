"""Pure-Python regression for PuTTY's absolute remote destinations; no Lean."""
from gcp_cfr import VM, scp_destination


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
    print('PASS: absolute SCP destination and four invalid-home controls')


if __name__ == '__main__':
    main()
