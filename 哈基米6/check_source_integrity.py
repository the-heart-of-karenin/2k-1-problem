"""Read-only preservation check of the existing registered-source hash chain."""
from pathlib import Path
from hashlib import sha256
import json

ROOT = Path(__file__).resolve().parent
PRIMARY = ROOT.parent/'2k+1'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    names = ['研究检查点_2026-10-10_结果143.json',
             '研究推进状态_2026-10-10_结果146至147.json']
    names += [f'研究推进状态_2026-10-11_结果{r}.json' for r in range(148, 162)]
    names += [f'研究推进状态_2026-10-12_结果{r}.json' for r in range(162, 171)]
    names += ['研究推进状态_2026-10-13_结果171.json']
    states = [json.loads((PRIMARY/name).read_text(encoding='utf-8')) for name in names]
    checked = {}
    for state in states:
        for name, expected in state['source_hashes'].items():
            source_path = (PRIMARY/name).resolve()
            assert source_path.is_relative_to(PRIMARY.resolve())
            actual = digest(source_path)
            assert actual == expected, ('registered source changed', name)
            assert name not in checked or checked[name] == actual
            checked[name] = actual
    assert digest(PRIMARY/names[0]) == states[1]['previous_checkpoint_sha256']
    for i in range(2, len(states)):
        assert digest(PRIMARY/names[i-1]) == states[i]['previous_state_sha256']
    assert states[-1]['latest_recorded_result'] == 171 and states[-1]['next_result'] == 172
    out = dict(status='PASS', main_status='OPEN',
               registered_sources_unchanged=len(checked),
               latest_primary_result=171, next_primary_result=172,
               primary_state_path=str(PRIMARY/names[-1]),
               primary_state_sha256=digest(PRIMARY/names[-1]),
               source_sha256=digest(Path(__file__)),
               check_is_file_integrity_not_independent_mathematical_reproof=True)
    (ROOT/'source_integrity.json').write_text(json.dumps(out, ensure_ascii=False, indent=2),
                                              encoding='utf-8')
    print(json.dumps(out, ensure_ascii=False))


if __name__ == '__main__':
    main()
