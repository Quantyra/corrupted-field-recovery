"""Pure-Python strict axiom-token regression; never invokes Lean."""
from gcp_cfr_runner import approved_axiom_profile, validate_type_block


def main():
    accepted = ['propext', 'Classical.choice', 'Quot.sound',
                'Classical.choice.{u}', 'Quot.sound.{u}',
                'propext, Classical.choice.{u_1}, Quot.sound.{u}']
    rejected = ['sorryAx', 'sorryAx.{u}', 'Project.axiom',
                'Lean.ofReduceBool', 'native_decide',
                'Project.Classical.choice.{u}', 'Classical.choice.spoof.{u}',
                'Classical.choice.{u} embedded', 'Classical.choice.{}',
                'Classical.choice.{u', 'Classical.choice.{u}}',
                'Classical.choice.{u;evil}', 'Classical.choice.{u,v}',
                'Classical.choice.{Type}', 'Quot.sound.{max}',
                'propext.{u}', 'propext, propext',
                'Classical.choice, Classical.choice.{u}', 'propext,']
    for value in accepted:
        approved_axiom_profile(value)
    for value in rejected:
        try:
            approved_axiom_profile(value)
        except ValueError:
            continue
        raise AssertionError('Accepted invalid profile: '+value)
    validate_type_block('Example : (h0 : P) → (h1 : Q) → P ∧ Q')
    validate_type_block('Example : (h0 : P) → (h1 : Q) → And P Q', ['h0', 'h1', 'And'])
    validate_type_block('Example : (h0 : P) → (h1 : Q) → P ∧ Q', ['h0', 'h1', 'And'])
    for text, expected in [('Example : Andromeda', ['And']),
                           ('Example : Other.And P Q', ['And']),
                           ('Example : αAnd', ['And']),
                           ('Example : P /- And -/', ['And']),
                           ('Example : "And"', ['And']),
                           ('Example : (h0 : P) → P', ['h0', 'h1'])]:
        try:
            validate_type_block(text, expected)
        except ValueError:
            continue
        raise AssertionError('Accepted missing/spoofed type token: '+text)
    for value in ['', 'Example : ⋯', 'Example : …', 'Example : ...']:
        try:
            validate_type_block(value)
        except ValueError:
            continue
        raise AssertionError('Accepted missing/truncated type: '+value)
    print(f'PASS: {len(accepted)} approved profiles; {len(rejected)} axiom and 4 truncation negative controls')


if __name__ == '__main__':
    main()
