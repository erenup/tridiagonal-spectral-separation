#!/usr/bin/env python3
"""Exact fixtures and reason-specific negative controls; identical under -O."""
import argparse
import copy
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise SystemExit('TEST FAILURE: '+message)


def module(name):
    spec = importlib.util.spec_from_file_location('test_'+name, ROOT/(name+'.py'))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def power(target):
    result = 0
    while 2**result < target:
        result += 1
    return result


def precision(n, d):
    return power(4*n*2**d)+2*power(16*n**3)+20+power(n*n)


def save(path, obj):
    path.write_text(json.dumps(obj, sort_keys=True, indent=2)+'\n')


def fixtures():
    # Each displayed source matrix is normalized by a rational absolute-row-sum
    # bound, using |re z|+|im z| as an upper bound for |z|.
    descriptions = [
        ('zero2', 2, [0, 0], [0], [0]),
        ('zero3', 4, [0]*3, [0]*2, [0]*2),
        ('repeated4', 3, [F(1,4), F(1,4), F(-1,4), F(-1,4)], [0]*3, [0]*3),
        ('complex2', 2, [F(1,4), F(-1,4)], [F(1,4)], [F(1,4)]),
        ('complex3', 5, [F(1,4), 0, F(-1,4)], [F(1,8)]*2, [F(1,16), F(-1,16)]),
        ('strong4', 2, [0]*4, [F(1,2)]*3, [0]*3),
        ('zero_edges8', 4, [F((-1)**i,4) for i in range(8)],
         [F(1,8) if i%3 else F(0) for i in range(7)],
         [F(1,16) if i%3 else F(0) for i in range(7)]),
        ('strong8', 2, [0]*8, [F(1,2)]*7, [0]*7),
        ('boundary8', 9, [F(1,2)]*8, [F(1,4)]*7, [0]*7),
        ('fractional_proxy3', 4, [F(1,3), F(-1,5), F(1,7)],
         [F(1,11), F(1,17)], [F(1,13), F(-1,19)]),
    ]
    p = precision(4, 6)
    descriptions.append(('weak4', 6, [0, 0, F(1,2), F(1,2)],
                         [F(1,2**p), 0, F(3,2**p)], [0, F(1,2**p), 0]))
    output = []
    for name, d, diagonal, real, imag in descriptions:
        diagonal, real, imag = [list(map(F, part)) for part in (diagonal, real, imag)]
        n = len(diagonal)
        Q = 2**precision(n, d)
        for i in range(n):
            bound = abs(diagonal[i])
            if i:
                bound += abs(real[i-1])+abs(imag[i-1])
            if i+1 < n:
                bound += abs(real[i])+abs(imag[i])
            require(bound <= 1, 'fixture is not exactly normalized: '+name)
        proxy = [[(v*Q).numerator//(v*Q).denominator for v in row]
                 for row in (diagonal, real, imag)]
        require(all(abs(F(w,Q)-v) <= F(1,Q)
                    for row, prox in zip((diagonal,real,imag),proxy) for v,w in zip(row,prox)),
                'proxy enclosure: '+name)
        data = {'schema': 'KE02.input.v1', 'n': n, 'd': d,
                'diagonal': proxy[0], 'edge_real': proxy[1], 'edge_imag': proxy[2]}
        source = {'diagonal': list(map(str,diagonal)), 'edge_real': list(map(str,real)),
                  'edge_imag': list(map(str,imag)), 'normalization': 'exact absolute row-sum bound ≤1'}
        output.append((name, data, source))
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    work = ROOT/'tmp'/('optimized' if sys.flags.optimize else 'normal')
    work.mkdir(parents=True, exist_ok=True)
    command = [sys.executable, '-I']+(['-O'] if sys.flags.optimize else [])
    checker = module('verify')
    producer = module('generate')
    long_input = {'schema':'KE02.input.v1','n':2,'d':15000,'diagonal':[10**4400,0],
                  'edge_real':[0],'edge_imag':[0]}
    long_path = work/'long_integer_roundtrip.json'
    save(long_path,long_input)
    require(checker.load(long_path) == long_input and producer.read_input(long_path) == long_input,
            'more than 4300 decimal digits must parse and serialize')
    loader_code = ('import runpy,sys,json; scope=runpy.run_path(sys.argv[1]); '
                   'obj=scope[sys.argv[3]](sys.argv[2]); print(json.dumps(obj,sort_keys=True))')
    for filename, function in [('generate.py','read_input'), ('verify.py','load')]:
        result = subprocess.run(command+['-c',loader_code,str(ROOT/filename),str(long_path),function],
                                capture_output=True,text=True)
        require(result.returncode == 0 and json.loads(result.stdout) == long_input,
                'fresh child long-integer loader: '+filename+' '+result.stderr)
    cases = [
        ([0,0], [1], 0, (1,0,1), 'zero pivot, nonzero edge'),
        ([0,7], [0], 0, (0,1,1), 'isolated zero'),
        ([1,1], [1], 0, (0,1,1), 'zero after Schur complement'),
        ([1,1,0], [1,1], 0, (1,0,2), 'later 2x2 pivot'),
        ([0,0,0], [1,1], 0, (1,1,1), '2x2 elimination leaves next diagonal unchanged'),
        ([0,0], [F(5,16)], 0, (1,0,1), 'complex edge squared magnitude'),
        ([2,2,-1,-1], [0,0,0], 2, (2,2,0), 'repeated eigenvalue endpoint'),
        ([0,0], [1], 1, (1,1,0), 'upper eigenvalue endpoint'),
        ([0,0], [1], -1, (0,1,1), 'lower eigenvalue endpoint'),
    ]
    for diag, sq, shift, answer, label in cases:
        observed = checker.exact_inertia(list(map(F,diag)),list(map(F,sq)),F(shift))
        require(observed == answer, 'inertia branch: '+label)
    sample = {'schema': 'KE02.input.v1','n':2,'d':2,'diagonal':[0,0],
              'edge_real':[1],'edge_imag':[2]}
    c = producer.Constructor(sample)
    require(c.count([0,0],2) == 1, 'negative-denominator floor (5//-2 must equal -3)')
    require(c.count([0,0],0) == 1 and c.stats['zero_replacements'] > 0,
            'safeguarded zero pivot with nonzero edge')
    sample['edge_real'] = [0]; sample['edge_imag'] = [0]
    c = producer.Constructor(sample)
    require(c.count([0,0],0) == 2 and c.stats['zero_replacements'] == 2,
            'safeguarded isolated zero pivots')
    positives, originals, certs = [], {}, {}
    sources = {}
    for name, data, source in fixtures():
        originals[name] = data
        sources[name] = source
        ip = ROOT/'fixtures'/(name+'.json')
        cp, sp = work/(name+'.certificate.json'), work/(name+'.stats.json')
        save(ip,data)
        generated = subprocess.run(command+[str(ROOT/'generate.py'),str(ip),str(cp),'--stats',str(sp)],
                                   capture_output=True,text=True)
        require(generated.returncode == 0, 'generation '+name+': '+generated.stderr)
        checked = subprocess.run(command+[str(ROOT/'verify.py'),str(ip),str(cp)],
                                 capture_output=True,text=True)
        require(checked.returncode == 0, 'verification '+name+': '+checked.stderr)
        result = json.loads(checked.stdout)
        stats = json.loads(sp.read_text())
        require(stats['value_calls'] == 8*power(16*data['n']**3), 'fixed value-call count')
        require(stats['spectral_calls'] == stats['value_calls']+3, 'fixed spectral-call count')
        require(stats['count_calls'] == stats['spectral_calls']*data['n']*stats['p'],
                'fixed bisection count')
        require(stats['max_pivot_bits'] <= 2*stats['p']+4, 'observed pivot size exceeds proof bound')
        require(stats['max_word_bits'] <= 2*stats['p']+16, 'observed word-size envelope')
        certs[name] = json.loads(cp.read_text())
        save(ROOT/'certificates'/(name+'.json'), certs[name])
        positives.append({'fixture':name,'verification':result,'construction':stats})
    save(ROOT/'fixtures/SOURCES.json', sources)
    baseline_input = originals['zero2']
    baseline_cert = certs['zero2']
    controls = []

    def bad(name, reason, alter_input=None, alter_cert=None, raw_input=None, raw_cert=None):
        inp, cert = copy.deepcopy(baseline_input), copy.deepcopy(baseline_cert)
        if alter_input:
            alter_input(inp)
        if alter_cert:
            alter_cert(cert)
        ip, cp = work/(name+'.input.json'), work/(name+'.cert.json')
        if raw_input is None:
            save(ip,inp)
        else:
            ip.write_text(raw_input(inp))
        if raw_cert is None:
            save(cp,cert)
        else:
            cp.write_text(raw_cert(cert))
        result = subprocess.run(command+[str(ROOT/'verify.py'),str(ip),str(cp)],
                                capture_output=True,text=True)
        prefix = 'FAIL['+reason+']:'
        require(result.returncode != 0 and result.stderr.startswith(prefix),
                f'control {name}: expected {prefix}, got {result.returncode}, {result.stderr}')
        controls.append({'control':name,'reason':reason})

    bad('altered_proxy', 'INPUT_BINDING',
        alter_cert=lambda c: c['input']['diagonal'].__setitem__(0,1))
    bad('swapped_proxy', 'INPUT_BINDING',
        alter_input=lambda x: x.update(copy.deepcopy(originals['complex2'])))
    bad('lower_enclosure', 'ENCLOSURE_LOWER',
        alter_cert=lambda c: c['intervals']['center'].__setitem__(0,[c['center_grid']+1,c['center_grid']+2]))
    bad('upper_enclosure', 'ENCLOSURE_UPPER',
        alter_cert=lambda c: c['intervals']['center'].__setitem__(0,[c['center_grid']-1,c['center_grid']]))
    bad('wide_interval', 'INTERVAL_WIDTH',
        alter_cert=lambda c: c['intervals']['center'][0].__setitem__(1,c['intervals']['center'][0][0]+8))
    bad('false_defect_bound', 'DEFECT_FORMULA',
        alter_cert=lambda c: c.__setitem__('defect_num',c['defect_num']-1))
    bad('defect_denominator', 'DEFECT_DENOMINATOR',
        alter_cert=lambda c: c.__setitem__('defect_den',c['defect_den']*2))
    bad('radius', 'PARAM_RADIUS',
        alter_cert=lambda c: c['parameters'].__setitem__('radius_grid',c['parameters']['radius_grid']+1))
    bad('precision', 'PARAM_PRECISION',
        alter_cert=lambda c: c['parameters'].__setitem__('p',c['parameters']['p']+1))
    bad('budget', 'PARAM_BUDGET',
        alter_cert=lambda c: c['parameters'].__setitem__('delta_den',c['parameters']['delta_den']*2))
    bad('a_formula', 'PARAM_FORMULA',
        alter_cert=lambda c: c['parameters'].__setitem__('a',c['parameters']['a']+1))
    bad('output_diagonal', 'OUTPUT_DIAGONAL',
        alter_cert=lambda c: c['diagonal_grid'].__setitem__(0,c['diagonal_grid'][0]+1))

    def exceed_budget(c):
        c['center_grid'] = c['parameters']['Q']//c['parameters']['delta_den']
        c['diagonal_grid'] = [j*c['center_grid'] for j in range(1,c['input']['n']+1)]
    bad('output_budget', 'OUTPUT_BUDGET', alter_cert=exceed_budget)
    bad('bool_input', 'INPUT_INT', alter_input=lambda x: x['diagonal'].__setitem__(0,False))
    bad('bool_embedded', 'INPUT_BINDING', alter_cert=lambda c: c['input']['diagonal'].__setitem__(0,False))
    bad('bool_precision', 'PARAM_INT', alter_cert=lambda c: c['parameters'].__setitem__('p',True))
    bad('bool_interval', 'INTERVAL_INT', alter_cert=lambda c: c['intervals']['center'][0].__setitem__(0,True))
    bad('unknown_field', 'CERT_SCHEMA', alter_cert=lambda c: c.__setitem__('extra',0))
    bad('float_json', 'JSON_NUMBER', raw_input=lambda x: json.dumps(x).replace('"n": 2','"n": 2.0'))
    bad('nonfinite_json', 'JSON_NUMBER', raw_cert=lambda c: '{"extra":NaN,'+json.dumps(c)[1:])
    bad('duplicate_input', 'JSON_DUPLICATE', raw_input=lambda x: '{"n":2,'+json.dumps(x)[1:])
    bad('duplicate_cert', 'JSON_DUPLICATE', raw_cert=lambda c: '{"schema":"KE02.certificate.v1",'+json.dumps(c)[1:])
    bad('malformed_json', 'JSON_SYNTAX', raw_cert=lambda c: json.dumps(c)+'{}')

    # A validly bounded proxy outside the necessary norm ball must be rejected.
    Q = baseline_cert['parameters']['Q']
    def overnorm_input(x):
        x['diagonal'] = [Q,Q]
        x['edge_real'] = [Q]
    def overnorm_cert(c):
        overnorm_input(c['input'])
    bad('proxy_norm', 'PROXY_NORM', alter_input=overnorm_input, alter_cert=overnorm_cert)

    # All enclosures in this control are genuine exact enclosures. At the bad
    # center T0+cX=0, so the convexity defect is large and must fail DEFECT_SMALL.
    bad_center = baseline_cert['parameters']['beta_grid']//2
    def collision_input(x):
        x['diagonal'] = [-j*bad_center for j in range(1,x['n']+1)]
    def collision_cert(c):
        collision_input(c['input'])
        n = c['input']['n']; r = c['parameters']['radius_grid']
        c['center_grid'] = bad_center
        c['diagonal_grid'] = [j*bad_center for j in range(1,n+1)]
        for key, offset in [('minus',-r),('center',0),('plus',r)]:
            eigenvalues = sorted(j*offset for j in range(1,n+1))
            c['intervals'][key] = [[v,v+1] for v in eigenvalues]
        low = sum(j*pair[0] for j,pair in enumerate(c['intervals']['center'],1))
        up = sum(j*pair[1] for key in ['minus','plus'] for j,pair in enumerate(c['intervals'][key],1))
        c['defect_num'] = up-2*low+10*n*(n+1)
    bad('genuine_bad_center', 'DEFECT_SMALL', alter_input=collision_input, alter_cert=collision_cert)
    report = {'status':'PASS','arithmetic':'integers and Fraction; no assertions or numerical eigensolver',
              'inertia_unit_cases':len(cases),'safeguarded_unit_cases':3,
              'long_integer_roundtrip_decimal_digits':4401,
              'long_integer_fresh_loaders':['generate.py','verify.py'],
              'positive_certificates':positives,'negative_controls':controls,
              'word_lengths':'corroboration of the written bound, not its proof'}
    args.report.parent.mkdir(parents=True,exist_ok=True)
    save(args.report,report)
    print(json.dumps({'status':'PASS','positive_certificates':len(positives),
                      'negative_controls':len(controls),'inertia_unit_cases':len(cases),
                      'safeguarded_unit_cases':3},sort_keys=True))


if __name__ == '__main__':
    main()
