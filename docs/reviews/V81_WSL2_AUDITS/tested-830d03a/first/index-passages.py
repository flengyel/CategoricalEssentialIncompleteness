from pathlib import Path
import json,re,subprocess
here=Path(__file__).resolve().parent
numbered=[json.loads(s) for s in (here/'numbered-sources.jsonl').read_text().splitlines()]
labels={r['printed'].split()[-1]:r['label'] for r in numbered}
active=subprocess.check_output(['git','show','830d03a5adcf144a003feb36f88bd06e0c5b0cf5:FORMALIZATION_STATUS_V81.md'],cwd=here,text=True).splitlines()
# A leading integer gives the first physical TeX line of a shared proof or construction.
# P<n> records a v81 application row by physical line in its frozen correspondence.
# L<n> names an independently checked literature passage below. A section marker shares its contents' context.
bands={
'abstract':[(1,'4.7 4.8'),(21,'5.1 5.3'),(32,'8.6 9.7 10.6')],
'01-introduction':[(1,'3.1 4.2'),(13,'4.7 4.8'),(30,'4.4 4.5 4.6'),(60,'4.7 4.8'),(74,'5.1 5.2 5.3'),(97,'6.1 7.1 8.6 D.1'),(124,'P42 9.3 9.7 L01 L02'),(144,'10.4 10.6 10.9 B.1'),(159,'L03 L04'),(173,'L05 L06 L07 L08 P29 3.3 C.1'),(189,'P30'),(198,'L09 L10'),(208,'L11 P29 4.7 5.3')],
'02-categorical':[(1,'3.1 A.7'),(28,'3.1 P31'),(44,'3.1 5.1 P31'),(71,'3.1 B.9 P31'),(90,'A.7 B.3'),(110,'P31 P32 3.4 B.3'),(170,'3.1 B.4'),(185,'P31 5.1 B.7 B.8')],
'03-sections':[(1,'3.1 P32'),(89,'3.2'),(108,'3.3 3.4'),(177,'C.1')],
'03a-internal':[(1,'A.1 A.2 A.3 A.4 A.5 A.6'),(52,'4.1'),(73,'4.1 A.7'),(142,'4.1 4.2'),(149,'4.2'),(209,'4.3'),(237,'4.3 P63 P64'),(256,'4.7 4.8')],
'03b-internal':[(1,'4.4 A.6'),(86,'4.4 4.5'),(171,'4.5'),(188,'4.6'),(323,'4.7 4.8'),(368,'4.7 P65')],
'04-theory':[(1,'5.1 5.2 5.3'),(12,'5.1'),(116,'5.1 5.2'),(131,'5.2'),(214,'5.2 P34'),(228,'5.3'),(350,'5.1 5.2 5.3 P116')],
'05-syntactic':[(1,'6.1 P35 P118'),(126,'6.1 P35'),(148,'P35'),(175,'6.1 P118'),(189,'6.1 6.3 P118'),(231,'6.1 6.3')],
'05a-internal':[(1,'6.2 6.3'),(244,'6.3 6.4 P36'),(277,'6.4 6.5 6.6 P126'),(522,'6.7 P130'),(657,'6.8 6.9'),(910,'6.9 A.7')],
'06-interpretation':[(1,'7.1'),(64,'7.2 7.3'),(125,'7.4'),(175,'7.5 7.6'),(348,'7.7 7.8 7.9'),(520,'7.8 7.9')],
'08-essential':[(1,'8.1 8.2 8.3'),(90,'8.2 8.3'),(239,'8.1 8.4 L12'),(288,'P39 8.1 8.4'),(316,'P40 L06'),(329,'8.9 8.10')],
'08a-uniform':[(1,'8.5'),(19,'P37 8.5'),(38,'8.5'),(121,'8.5 8.6'),(311,'8.5')],
'08b-uniform':[(1,'P67 L13 8.6'),(11,'8.6 P41')],
'08c-numerical':[(1,'8.7'),(463,'8.7 8.8'),(491,'8.8'),(573,'8.8')],
'08d-numerical':[(1,'8.3 8.4 8.8'),(61,'8.4 P39')],
'04-miller':[(1,'L01 P42 9.1'),(48,'9.1'),(108,'9.2'),(209,'9.3 9.4 P43'),(328,'9.5 9.6 9.7'),(558,'9.7 P44 P45'),(654,'9.8')],
'09-three':[(1,'B.1 B.2 P46'),(45,'B.2 B.3'),(81,'B.4 B.5 B.6'),(121,'B.7 B.8 B.9'),(148,'3.3 3.4 10.1'),(180,'10.1 P47'),(279,'10.2 10.3 10.4 P48'),(442,'10.3 10.4'),(502,'10.4 10.5 P49'),(546,'10.5 10.6 P49'),(624,'10.7 10.8'),(813,'10.9')],
'a-syntax':[(1,'A.1 A.2 P50 P51'),(119,'A.1 A.2'),(236,'A.3'),(370,'A.4 A.5 L14'),(411,'A.4 A.5'),(416,'A.5 L15'),(420,'A.5'),(452,'A.6'),(534,'A.7'),(564,'A.7'),(570,'A.7 P52'),(588,'4.1 A.7'),(596,'A.5 A.6 5.3 P53')],
'b-three':[(1,'B.1'),(46,'B.1 B.2'),(61,'B.2'),(135,'B.3 B.4'),(252,'B.5 B.6'),(341,'B.7 P47'),(491,'B.8 B.9'),(573,'B.9 B.10 P54')],
'c-section':[(1,'3.1 3.2 C.1 L08'),(105,'C.1 P55'),(206,'C.1 3.3')],
'd-faithful':[(1,'D.1'),(61,'D.1 P56 L16'),(64,'D.1 P124'),(91,'D.2'),(121,'D.2 P57'),(148,'8.1 8.4 D.2'),(181,'D.2 P57')],
'e-reading':[(1,'4.7'),(42,'4.8'),(70,'8.9'),(107,'3.1 C.1'),(136,'5.3'),(168,'8.6 P41'),(190,'9.6 9.7 P44')],
}
# Specific published assertions and their formal status. Literature-only mathematical statements
# are indexed even when a numbered result on the same page is independent of them.
external={
'L01':'Miller 6.3/Bauer–Hanson 2.2, actual sequence proved in V46MillerFixedPoint:125',
'L02':'Bauer–Hanson 6.4, internal Dedekind reals epi in T_mu, external theorem open',
'L03':'Heller 9.2, Turing completion of a uniformly generated isotypical B# in locally connected iteration category, open',
'L04':'Lengyel 2004 26, faithful iteration functor to separated target and Turing completion, open',
'L05':'Di Paola–Heller 8.15, unrestricted sum-valued Turing evaluation refuted at zero identity; corrected nonzero c+ case open',
'L06':'Bernardi §§2–3, categorical fixed points and saturated domains open; numerical classes, unions and PA totalizer proved',
'L07':'Montagna Remark 3.1, categorical binary productive morphism in unprimed S open',
'L08':'Lengyel 2006 4.1 as stated refuted by Appendix C under its printed structures',
'L09':'Historical discussion of GL and diagonalizable algebras, no formal input to v81',
'L10':'van Dijk–Gietelink Oldenziel 5.19 and 5.20 in the internal arithmetic universe, two conclusions open',
'L11':'Cockett–Hofstra 4.9, PCA computability, converse and idempotent splitting open; 3.4 recognition proved',
'L12':'Di Paola–Heller numerical result (3), journal page 595; strong numeralwise definability supplies the reduction',
'L13':'Pour-El property versus unrestricted existence; undefined reading refuted, PA assignment proved with a single chosen q',
'L14':'Aczel arbitrary finitary set rules = finite tree proofs, original generality outside located kernel applications; A.5 case proved',
'L15':'Wißmann 3.6 arbitrary factorization system lifted to Alg(F), outside located applications; A.5 regular slice case proved',
'L16':'Di Paola–Montagna 4.4 on the unprimed S_T, V46SyntacticNonLocalConnectedness:236; C.1 uses different source',
}
rs=[json.loads(l) for l in (here/'reading-order.jsonl').read_text().splitlines()]; ownlabels={r['label'] for r in numbered};out=[]
for r in rs:
    base=Path(r['path']).stem; k=next((p for p in bands if base.startswith(p)),None)
    scope=[]
    if k:
        lo=max((n for n,_ in bands[k] if n<=r['line']),default=1)
        for n,ss in bands[k]:
            if lo<=n<=r['end']: scope.extend(ss.split())
    if r['claim'] in ownlabels:
        # The local proof is primary. Retain distinct explicitly located unnumbered applications.
        scope=[x for x in scope if not x in labels]
    local=[*([r['claim']] if r['claim'] in ownlabels else []),*(c for c in r['references'] if c in ownlabels),*(labels[x] for x in scope if x in labels)]
    apps=[int(x[1:]) for x in scope if x.startswith('P')];hist=[x for x in scope if x in external]
    modules=[]
    for i in apps:
        modules.extend(re.findall(r'\((Lean/[^) ]+?\.lean)(?:#(L\d+))?\)',active[i-1]))
    cite={r['id']:r['citations'] for r in (r,) if r['citations']}
    e={'id':r['id'],'path':r['path'],'line':r['line'],'end':r['end'],'kind':r['kind'],'numbered_rows':list(dict.fromkeys(local)),'current_correspondence_lines':list(dict.fromkeys(apps)),'supplementary_Lean_locations':list(dict.fromkeys(modules)),'literature':list(dict.fromkeys(hist)), 'cites':r['citations'],'reconstruction_section':r['section']}
    if r['kind']=='bibliographic entry':e['role']='Bibliographic metadata. Read claim at the actual citation site.'
    elif k is None:e['role']='Typesetting, metadata, or manuscript inclusion.'
    else:e['role']='Printed claim, proof, comparison or local definition. See the indicated source proofs and the independent reconstruction.'
    out.append(e)
assert len(out)==667
(here/'passage-index.jsonl').write_text('\n'.join(json.dumps(e,ensure_ascii=False) for e in out)+'\n')
(here/'external-keys.json').write_text(json.dumps(external,ensure_ascii=False,indent=2)+'\n')
print('blocks',len(out),'with source groups',sum(bool(e['numbered_rows'] or e['literature'] or e['supplementary_Lean_locations']) for e in out))
