"""构建证明、核对公理，再由 Lean 自带检查器重新检查各模块。"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    'SunPrize.Basic',
    'SunPrize.Tables',
    'SunPrize.Graph',
    'SunPrize.Obstruction',
    'SunPrize.Extension',
    'SunPrize.Certificates.sevenClassificationContradiction',
    'SunPrize.Certificates.normalizedFifteenContradiction',
    'SunPrize.Classification',
    'SunPrize.Main',
    'SunPrize.Erdos1216',
]
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def run(arguments: list[str]) -> dict:
    started = time.monotonic()
    result = subprocess.run(arguments, cwd=ROOT, text=True, encoding='utf-8',
                            errors='replace', capture_output=True, check=False)
    print(result.stdout, end='', flush=True)
    print(result.stderr, end='', flush=True)
    if result.returncode != 0:
        raise RuntimeError(f'检查失败，退出码 {result.returncode}：{arguments}')
    return {'command': arguments, 'seconds': round(time.monotonic() - started, 3),
            'stdout': result.stdout, 'stderr': result.stderr, 'exit_code': 0}


def main() -> None:
    sources = sorted((ROOT / 'SunPrize').rglob('*.lean')) + [ROOT / 'SunPrize.lean']
    forbidden = re.compile(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|unsafe|opaque)\b', re.M)
    for path in sources:
        if forbidden.search(path.read_text(encoding='utf-8')):
            raise RuntimeError(f'证明源文件含有待审查的声明或占位：{path}')
    records = [run(['lake', 'build'])]
    audit = run(['lake', 'env', 'lean', 'scripts/Audit.lean'])
    records.append(audit)
    axioms = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit['stdout'])
    if len(axioms) != 6:
        raise RuntimeError(f'公理审计输出不完整：{len(axioms)} / 6')
    for theorem, names in axioms:
        found = {name.strip() for name in names.split(',') if name.strip()}
        if not found <= ALLOWED_AXIOMS:
            raise RuntimeError(f'{theorem} 使用了额外公理：{found - ALLOWED_AXIOMS}')
    for module in MODULES:
        print(f'重新检查模块：{module}', flush=True)
        records.append(run(['lake', 'env', 'leanchecker', module]))
    report = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'description': '本地构建、公理审计和同一 Lean 内核的声明重放；不代表第三方评审或官方核验。',
        'lean': run(['lake', 'env', 'lean', '--version'])['stdout'].strip(),
        'mathlib_commit': 'db584cd6d46c92f209a44c0f1c829460d327499d',
        'hash_normalization': '源码按 UTF-8 解码，将换行统一为 LF 后计算 SHA-256。',
        'axioms': {theorem: names.split(', ') for theorem, names in axioms},
        'source_sha256': {str(path.relative_to(ROOT)).replace('\\', '/'):
            hashlib.sha256(path.read_text(encoding='utf-8').encode('utf-8')).hexdigest() for path in sources},
        'checks': records,
    }
    output = ROOT / '.research-cache' / 'verification.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(f'全部检查通过，报告：{output}', flush=True)


if __name__ == '__main__':
    main()
