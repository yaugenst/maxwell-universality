#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "matplotlib>=3.9,<4"]
# ///
"""Device anatomy and operation, derived from the saved full Maxwell basis fields."""
from pathlib import Path
import argparse
from itertools import product, combinations
from hashlib import sha256
import json

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import Normalize, TwoSlopeNorm
from matplotlib.patches import Circle
import numpy as np

ROOT=Path(__file__).parent
CASE=ROOT/'results/direct_refinement_a/signed_spd/h0.14285714'
OUT=ROOT/'report/device_walkthrough'
COLORS=['#2563b6','#d27b13','#7c4da8','#8995a2','#8995a2','#8995a2']
LABELS=['T1','T2','T3','A1','A2','A3']
INK='#1d2938'


def read(path):
    return json.loads(path.read_text())


def center_vectors(values,n,h):
    """Interpolate edges to cell centers; use only for visualization."""
    shapes=[tuple(n[k]-(k!=j) for k in range(3)) for j in range(3)]
    offsets=np.r_[0,np.cumsum([np.prod(s) for s in shapes])]
    result=[]
    for j,shape in enumerate(shapes):
        v=values[offsets[j]:offsets[j+1]].reshape((*shape,values.shape[1]))/np.sqrt(h**3)
        for axis in range(3):
            if axis==j:
                continue
            pad=[(0,0)]*4
            pad[axis]=(1,1)
            v=np.pad(v,pad)
            a,b=[slice(None)]*4,[slice(None)]*4
            a[axis],b[axis]=slice(None,-1),slice(1,None)
            v=(v[tuple(a)]+v[tuple(b)])/2
        result.append(v)
    return np.stack(result,axis=-2)


def section(values):
    mid=values.shape[1]//2
    return (values[:,mid-1]+values[:,mid])/2


def defect(x,y,z,c,v):
    r2=(x-c[0])**2+(y-c[1])**2+(z-c[2])**2
    q=np.zeros_like(r2)
    mask=r2<1
    q[mask]=v*np.exp(-1/(1-r2[mask]))
    return q


def outlines(ax,centers,colors=COLORS,labels=True):
    for i,c in enumerate(centers):
        ax.add_patch(Circle((c[0],c[2]),1,fill=False,color=colors[i],lw=1.15,ls='-' if i<3 else '--',alpha=.9))
        if labels:
            ax.text(c[0],c[2]+1.08,LABELS[i],ha='center',va='bottom',color=INK,fontsize=10,
                    bbox=dict(facecolor='white',edgecolor='none',alpha=.86,pad=1.2))
    ax.set(xlim=(-4,4),ylim=(-4,4),xlabel='x',ylabel='z',aspect='equal',xticks=[-4,-2,0,2,4],yticks=[-4,-2,0,2,4])


def save(fig,name):
    for ext in ('png','pdf'):
        fig.savefig(OUT/f'{name}.{ext}',dpi=210,bbox_inches='tight',facecolor='white')
    plt.close(fig)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inline-output',type=Path)
    args=parser.parse_args()
    OUT.mkdir(exist_ok=True)
    r=read(CASE/'verification.json');m=read(CASE/'metadata.json'); a=np.load(CASE/'verification_fields.npz')
    c=np.array(m['centers']);v=np.array(r['strengths']);nominal=np.array(r['nominal_source_decoder_strengths'])
    alpha=r['alpha'];gamma=np.array(r['target']);n=a['shape'];h=float(a['h'])
    E=center_vectors(a['fields'],n,h);F=center_vectors(a['sources'],n,h);B=center_vectors(a['probes'],n,h)
    Es,Fs,Bs=map(section,(E,F,B))
    response=alpha*np.diag(nominal)+nominal[:,None]*(a['probes'].T@a['fields'])
    assert np.linalg.norm(response-np.array(r['decoded_response_real']))<1e-12
    assert np.linalg.norm(a['sources']-alpha*a['probes']*nominal)<1e-12
    ref=np.linalg.solve(gamma,np.eye(3)) # Comparison only; never used to create the fields or source.
    xcoord=(np.arange(n[0])+.5)*h-4; zcoord=(np.arange(n[2])+.5)*h-4
    xx,zz=np.meshgrid(xcoord,zcoord,indexing='ij'); base=7+m['bloch_probe']['ec']-.3
    bg=base+.5*(np.cos(np.pi*xx)+2+4*np.cos(np.pi*zz))
    bumps=sum(defect(xx,0,zz,ci,vi) for ci,vi in zip(c,v))
    eps=bg+bumps
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11,'axes.titlesize':13,
                         'axes.labelsize':11,'text.color':INK,'axes.labelcolor':INK,
                         'axes.spines.top':False,'axes.spines.right':False,'axes.titleweight':'medium'})

    # Anatomy: true dimensions and smooth scalar material, no invented connections.
    fig=plt.figure(figsize=(13,8.3),layout='constrained')
    gs=fig.add_gridspec(2,3,width_ratios=[1.15,1,1],height_ratios=[1,.65])
    ax=fig.add_subplot(gs[0,0],projection='3d')
    vertices=np.array(list(product([-4,4],[-3,3],[-4,4])))
    bx,bz=np.meshgrid(np.linspace(-4,4,65),np.linspace(-4,4,65))
    by=np.full_like(bx,3.)
    back=base+.5*(np.cos(np.pi*bx)+2*np.cos(np.pi*by)+4*np.cos(np.pi*bz))
    ax.plot_surface(bx,by,bz,facecolors=plt.get_cmap('viridis')((back-4.77)/(21.24-4.77)),
                    alpha=.32,shade=False,linewidth=0,rasterized=True)
    fx,fy=np.meshgrid(np.linspace(-4,4,65),np.linspace(-3,3,49))
    floor=base+.5*(np.cos(np.pi*fx)+2*np.cos(np.pi*fy)+4)
    ax.plot_surface(fx,fy,np.full_like(fx,-4),facecolors=plt.get_cmap('viridis')((floor-4.77)/(21.24-4.77)),
                    alpha=.3,shade=False,linewidth=0,rasterized=True)
    for p,q in combinations(vertices,2):
        if np.count_nonzero(p!=q)==1:
            ax.plot(*np.stack([p,q]).T,color='#8a96a4',lw=.8,alpha=.75)
    u,w=np.meshgrid(np.linspace(0,2*np.pi,40),np.linspace(0,np.pi,24))
    for i,(ci,vi) in enumerate(zip(c,v)):
        # An actual isosurface of each smooth dielectric increment at 25% of its peak.
        rad=np.sqrt(1-1/(1-np.log(.25)))
        ax.plot_surface(ci[0]+rad*np.sin(w)*np.cos(u),ci[1]+rad*np.sin(w)*np.sin(u),ci[2]+rad*np.cos(w),
                        color=COLORS[i],alpha=.5,linewidth=0,shade=True,rasterized=True)
        ax.text(ci[0],ci[1]-.95,ci[2]+.22,LABELS[i],color=INK,ha='center',fontsize=11)
    ax.set(xlim=(-4.4,4.4),ylim=(-3.4,3.4),zlim=(-4.4,4.4),xlabel='x',ylabel='y',zlabel='z',
           xticks=[-4,0,4],yticks=[-3,0,3],zticks=[-4,0,4])
    ax.set_box_aspect((8,6,8));ax.view_init(elev=14,azim=-70)
    ax.grid(False)
    for axis in (ax.xaxis,ax.yaxis,ax.zaxis):
        axis.pane.fill=False;axis.pane.set_edgecolor('white')
    ax.set_title('a  Six defects in one 3D cavity',pad=20,loc='left')
    ac=fig.add_subplot(gs[1,0]);ac.axis('off')
    ac.text(0,.96,'Read the cutaway',fontsize=13,weight='medium',va='top')
    ac.text(0,.77,'Outer box: 8 × 6 × 8 PEC cavity.\n\nColored surfaces: 25% of each defect peak;\nthey are not sharp material interfaces.\n\nT1–T3 carry input sources and readouts.\nA1–A3 tune the shared cavity response.\n\nCircles in the sections mark the full\nradius-one support of each defect.',va='top',fontsize=10.5,linespacing=1.3)
    ax1=fig.add_subplot(gs[0,1]);im=ax1.imshow(bg.T,extent=(-4,4,-4,4),origin='lower',cmap='viridis',vmin=4.77,vmax=21.24)
    ax1.set_title('b  Periodic background',loc='left');outlines(ax1,c,labels=False)
    ax2=fig.add_subplot(gs[0,2]);ax2.imshow(eps.T,extent=(-4,4,-4,4),origin='lower',cmap='viridis',vmin=4.77,vmax=21.24)
    ax2.set_title('c  Background + six defects',loc='left');outlines(ax2,c)
    fig.colorbar(im,ax=[ax1,ax2],label='Relative permittivity ε at y = 0',fraction=.035,pad=.025)
    ar=fig.add_subplot(gs[1,1]);rr=np.linspace(-1.2,1.2,500)
    for i in [0,1,2,4]:
        ar.plot(rr,defect(rr,np.zeros_like(rr),np.zeros_like(rr),[0,0,0],v[i]),color=COLORS[i],label=LABELS[i],lw=2)
    ar.set(title='d  A defect is a smooth material bump',xlabel='Distance from defect center',ylabel='Added permittivity Δε',xlim=(-1.2,1.2))
    ar.axhline(0,color='#9aa4af',lw=.7);ar.legend(ncol=2,fontsize=9,frameon=False);ar.grid(alpha=.12)
    at=fig.add_subplot(gs[1,2]);at.axis('off')
    at.text(0,.96,'What the geometry means',va='top',fontsize=13,weight='medium')
    at.text(0,.77,'• Every site is a positive dielectric bump.\n\n• The background fills the entire box.\n\n• No internal metal, wires or waveguides.\n\n• All centers lie in y = 0; fields are 3D.\n\n• Lengths are in the solver’s units.',va='top',fontsize=10.5,linespacing=1.25)
    save(fig,'device_anatomy')

    # Actual source -> whole-cavity field -> signed volume moments.
    fig=plt.figure(figsize=(13,8),layout='constrained');gs=fig.add_gridspec(2,3,height_ratios=[1,.57])
    axes=[fig.add_subplot(gs[0,j]) for j in range(3)]
    src=np.linalg.norm(Fs[:,:,:,0],axis=-1);energy=np.sum(Es[:,:,:,0]**2,axis=-1)
    density=np.einsum('xzci,xzc,i->xz',Bs,Es[:,:,:,0],nominal)
    for ax,data,cmap,norm,title,clabel in [
        (axes[0],src/src.max(),'magma',Normalize(0,1),'1  Drive T1: b = (1, 0, 0)','Source magnitude / maximum'),
        (axes[1],np.log10(np.maximum(energy/energy.max(),1e-6)),'magma',Normalize(-6,0),'2  Solve the full cavity field','log₁₀ of |E|² / maximum'),
        (axes[2],density,'RdBu_r',TwoSlopeNorm(0,-abs(density).max(),abs(density).max()),'3  Integrate signed field moments','Weighted overlap density')]:
        im=ax.imshow(data.T,extent=(-4,4,-4,4),origin='lower',cmap=cmap,norm=norm)
        outlines(ax,c);ax.set_title(title,loc='left');fig.colorbar(im,ax=ax,orientation='horizontal',fraction=.055,pad=.12,label=clabel)
    ax=fig.add_subplot(gs[1,:2]);pos=np.arange(3);direct=alpha*nominal*np.array([1,0,0]);moment=response[:,0]-direct
    ax.barh(pos-.17,direct,height=.26,color='#c5ccd4',label='Known input contribution')
    ax.barh(pos-.17,moment,left=direct,height=.26,color=COLORS[:3],alpha=.85,label='Measured field contribution')
    ax.scatter(ref[:,0],pos+.16,marker='D',color=INK,s=35,label='Reference Γ⁻¹b',zorder=4)
    for i in range(3):
        ax.text(response[i,0]+(.009 if response[i,0]>=0 else -.009),i-.17,f'{response[i,0]:+.6f}',va='center',ha='left' if response[i,0]>=0 else 'right',fontsize=10)
    ax.set(yticks=pos,yticklabels=LABELS[:3],xlabel='Decoded answer x',title='4  Add the known input term to the measured moments',xlim=(-.13,.43))
    ax.invert_yaxis();ax.axvline(0,color='#84909d',lw=.8);ax.legend(loc='lower right',fontsize=9,frameon=False);ax.grid(axis='x',alpha=.12)
    ax=fig.add_subplot(gs[1,2]);ax.axis('off')
    ax.text(0,.96,'The answer is not field intensity',fontsize=12,weight='medium',va='top')
    ax.text(0,.74,r'$f=\alpha B V b$'+'\n'+r'$x=\alpha Vb+VB^{T}E$'+'\n\nSigned overlaps allow negative answers\nwith entirely positive permittivity.\n\nRelative equation error for this input:\n'+f'{100*np.linalg.norm(gamma@response[:,0]-np.eye(3)[:,0]):.4f}%',va='top',fontsize=11,linespacing=1.45)
    save(fig,'device_operation')

    # Basis response and exact superposition using saved field solutions.
    fig,axs=plt.subplots(2,3,figsize=(12.4,8.0),layout='constrained',gridspec_kw={'height_ratios':[1,.72]})
    maxabs=float(abs(Es).max())
    for j in range(3):
        im=axs[0,j].imshow(Es[:,:,2,j].T,extent=(-4,4,-4,4),origin='lower',cmap='RdBu_r',vmin=-maxabs,vmax=maxabs)
        outlines(axs[0,j],c);axs[0,j].set_title(f'Drive T{j+1} only: signed E_z',loc='left')
    fig.colorbar(im,ax=list(axs[0]),label='E_z, one shared scale',fraction=.022,pad=.02)
    ax=axs[1,0];lim=abs(response).max()
    im=ax.imshow(response,cmap='RdBu_r',vmin=-lim,vmax=lim)
    for i in range(3):
        for j in range(3):
            ax.text(j,i,f'{response[i,j]:+.4f}',ha='center',va='center',color='white' if abs(response[i,j])>.65*lim else INK,fontsize=11)
    ax.set(xticks=range(3),xticklabels=LABELS[:3],yticks=range(3),yticklabels=['x₁','x₂','x₃'],xlabel='Driven terminal',title='Measured solution map X ≈ Γ⁻¹')
    mixed=np.array([1,-.6,.8]);em=np.einsum('xzci,i->xzc',Es,mixed)
    im=axs[1,1].imshow(em[:,:,2].T,extent=(-4,4,-4,4),origin='lower',cmap='RdBu_r',vmin=-maxabs,vmax=maxabs)
    outlines(axs[1,1],c,labels=False);axs[1,1].set_title('A mixed input: b = (1, −0.6, 0.8)',loc='left')
    ax=axs[1,2];ax.axis('off')
    xm=response@mixed;err=np.linalg.norm(gamma@xm-mixed)/np.linalg.norm(mixed)
    ax.text(0,.97,'One fixed medium, many inputs',fontsize=13,weight='medium',va='top')
    ax.text(0,.78,'The three basis fields above determine\nthe response to every input:\n\nE(b) = b₁E₁ + b₂E₂ + b₃E₃\n\nFor the mixed input, decoded x is\n'+ '\n'.join(f'  x{i+1} = {val:+.6f}' for i,val in enumerate(xm))+f'\n\nRelative equation error: {100*err:.4f}%',va='top',fontsize=11,linespacing=1.5)
    save(fig,'device_basis_fields')

    # Compact, inline data: all input changes combine fields before squaring.
    def rounded(values):
        return np.array([float(f'{q:.6g}') for q in np.asarray(values).ravel()]).reshape(np.shape(values)).tolist()
    payload={'n':int(n[0]),'h':h,'centers':c.tolist(),'strengths':v.tolist(),'nominal':nominal.tolist(),
             'base':base,'rho':.5,'radius':1,'alpha':alpha,'target':gamma.tolist(),'response':response.tolist(),
             'source':rounded(Fs.transpose(3,2,1,0)),'field':rounded(Es.transpose(3,2,1,0)),
             'material':rounded(eps.T),'case':str(CASE.relative_to(ROOT)),
             'worstResidual':r['worst_relative_equation_residual']}
    (OUT/'device_data.json').write_text(json.dumps(payload,separators=(',',':')))
    if args.inline_output:
        template=(ROOT/'device_walkthrough.html').read_text()
        assert template.count('__DEVICE_DATA__')==1
        fragment=template.replace('__DEVICE_DATA__',json.dumps(payload,separators=(',',':')))
        assert len(fragment.encode())<1_000_000
        args.inline_output.parent.mkdir(parents=True,exist_ok=True)
        args.inline_output.write_text(fragment)
    evidence={'case':str(CASE.relative_to(ROOT)),'raw_fields_sha256':sha256((CASE/'verification_fields.npz').read_bytes()).hexdigest(),
              'source_and_decoder_reconstructed':True,'plane':'y=0, linear interpolation of cell-centered vector components',
              'geometry_isosurface':'25% of each local added-permittivity peak; not a material boundary',
              'visualization_only_interpolation':True,'quantitative_decoding':'Original staggered fields and probes, no spatial interpolation',
              'basis_input':{'b':[1,0,0],'decoded_x':response[:,0].tolist(),'equation_error':float(np.linalg.norm(gamma@response[:,0]-np.eye(3)[:,0]))},
              'mixed_input':{'b':mixed.tolist(),'decoded_x':xm.tolist(),'equation_error':float(err)},
              'interpretation':'Frequency-domain phasors. No time evolution, energy-flow trajectories, fabricated ports or theorem-scale construction is depicted.'}
    (OUT/'visualization_evidence.json').write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps({'output':str(OUT),'payload_bytes':(OUT/'device_data.json').stat().st_size,'evidence':evidence},indent=2))


if __name__=='__main__':
    main()
