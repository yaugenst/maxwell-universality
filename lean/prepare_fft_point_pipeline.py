#!/usr/bin/env python3
"""Assemble one sequential point-check queue, reusing proved direct transforms."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
P=ROOT/'evidence/fft_stage_proposals';Q=ROOT/'evidence/point_inertia_proposals'
OUT=ROOT/'Maxwell/Certificate/FFTWitness'
def read(path):return json.loads(path.read_text())
def full(name):return 'Maxwell.Certificate.FFTWitness.'+name
def raw_x_modules(modules):
    path=P/'raw_x_replacements.json'
    replaced=set(read(path)) if path.exists() else set()
    out=[]
    for module in modules:
        name=module.rsplit('.',1)[-1]
        if name.endswith('ListInputX') and name[:-10] in replaced:
            continue
        if name.endswith('ListCheckXBlocks') and name[:-16] in replaced:
            prefix=name[:-16]
            constants='ForwardConstants' if 'Forward' in prefix else 'InverseConstants'
            base='Maxwell.Certificate.FFTRawWitness.'
            out += [base+constants,base+constants+'Sound',base+prefix+'RawX',base+prefix+'RawXSound']
        else:
            out.append(module)
    return list(dict.fromkeys(out))

def main():
    old=read(P/'manifest.json')['modules'];new=read(P/'list_modules.json')
    status=read(P/'kernel_checks.json')['modules'];selected=[];inverse=[new[0]]
    # Ordinary column proofs already completed before list optimization remain
    # genuine proof dependencies. Expose the same public wrapper in either case.
    for label in ['Lower','Upper']:
      for d in range(3):
       for c in range(28):
        prefix=f'{label}D{d}C{c:02}'
        if status.get(prefix+'Complete',{}).get('exit_code')==0:
          selected.append(prefix)
          inverse += [full(m) for m in old if m.startswith(prefix)]
          s=f'''import Maxwell.Certificate.FFTWitness.{prefix}Complete
namespace Maxwell.Certificate.FFTWitness
open Matrix FourierBinding Maxwell.Spectral.PrimitiveYee

theorem {prefix}_list_inverse_contains (v : Cell → ℂ)
    (hv : DyadicFFT.Contains 52 {prefix}Input v) :
    DyadicFFT.Contains 52 {prefix}Result (transform 0 *ᵥ v) :=
  {prefix}_inverse_contains v hv

theorem {prefix}_list_native_inverse_contains (v : Cell → ℂ)
    (hv : DyadicFFT.Contains 52 {prefix}Input v) :
    DyadicFFT.Contains 52 {prefix}Native (transform 0 *ᵥ v) :=
  {prefix}_native_inverse_contains v hv
end Maxwell.Certificate.FFTWitness
'''
          (OUT/f'{prefix}ListComplete.lean').write_text(s)
          inverse.append(full(prefix+'ListComplete'))
        else:inverse += [m for m in new if m.rsplit('.',1)[-1].startswith(prefix)]
    # Restore the uniform public aggregation interface after earlier experiments.
    aggregate=(OUT/'InverseListComplete.lean').read_text()
    for prefix in selected:
        aggregate=aggregate.replace(prefix+'Complete',prefix+'ListComplete').replace(prefix+'_native_inverse_contains',prefix+'_list_native_inverse_contains')
    (OUT/'InverseListComplete.lean').write_text(aggregate)
    inverse.append(full('InverseListComplete'))
    forward=read(P/'forward_list_modules.json')
    material=read(Q/'material_modules.json')
    projection=read(Q/'projection_modules.json')
    curl=read(Q/'curl_modules.json')
    action=read(Q/'action_modules.json')
    complete=read(Q/'action_complete_modules.json')
    modules=[new[0],forward[0]]+material[:3]
    chains={label:list(modules) for label in ['Lower','Upper']}
    order=[('Lower',0),('Lower',1),('Upper',0),('Upper',1)]
    order += [(label,c) for c in range(2,28) for label in ['Lower','Upper']]
    for label,c in order:
        start=len(modules)
        index=(0 if label=='Lower' else 28)+c
        modules+=projection[5*index:5*index+5]
        modules += [full(f'{label}D{d}C{c:02}Input') for d in range(3)]
        modules.append(curl[index])
        for d in range(3):
            prefix=f'{label}D{d}C{c:02}'
            modules += [m for m in inverse if m.rsplit('.',1)[-1].startswith(prefix)]
        modules += [full(f'{label}ForwardD{d}C{c:02}Input') for d in range(3)]
        modules += [f'Maxwell.Certificate.MaterialWitness.{label}D{d}C{c:02}' for d in range(3)]
        for d in range(3):
            prefix=f'{label}ForwardD{d}C{c:02}'
            modules += [m for m in forward if m.rsplit('.',1)[-1].startswith(prefix)]
        modules += [action[index],complete[index]]
        chains[label] += modules[start:]
    aggregation=[full('InverseListComplete')]
    modules.append(full('InverseListComplete'))
    if (Q/'semantic_column_modules.json').exists():
        aggregation += read(Q/'semantic_column_modules.json')
        modules += read(Q/'semantic_column_modules.json')
    (P/'point_pipeline_modules.json').write_text(json.dumps(raw_x_modules(modules),indent=2)+'\n')
    for label,chain in chains.items():
        (P/f'point_{label.lower()}_modules.json').write_text(json.dumps(raw_x_modules(chain),indent=2)+'\n')
    (P/'point_aggregation_modules.json').write_text(json.dumps(aggregation,indent=2)+'\n')
    (P/'inverse_reused_original_columns.json').write_text(json.dumps(selected,indent=2)+'\n')
    print(f'{len(raw_x_modules(modules))} modules; {len(selected)} completed direct transforms reused.')

if __name__=='__main__':main()
