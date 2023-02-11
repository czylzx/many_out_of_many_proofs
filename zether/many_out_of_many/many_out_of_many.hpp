/***********************************************************************************
this hpp implements many_out_of_many proof 
***********************************************************************************/
#ifndef MANY_OUT_OF_MANY_HPP_
#define MANY_OUT_OF_MANY_HPP_
#include "../../crypto/ec_point.hpp"
#include "../../crypto/hash.hpp"
//#include "../../pke/twisted_elgamal.hpp"
#include "../../commitment/pedersen.hpp"
#include "../../utility/polymul.hpp"
//#include "../zkp/nizk/nizk_enc_relation.hpp"
//#include "../zkp/nizk/nizk_dlog_equality.hpp"
#include <utility>
#include <iostream>
//#include "innerproduct_proof.hpp" 

namespace ManyOutOfMany{
// define structure of ManyOutOfManyProof
struct PP
{
    Pedersen::PP com_part;
    size_t Com_LEN;
    size_t Log_Com_Len;
    size_t o;
    std::vector<std::vector<BigInt> >vec_xi;
   
};

struct Ck
{
    ECPoint gk;
    ECPoint hk;
};
struct Instance
{
    size_t Com_Num;
    std::vector<ECPoint> vec_com;
};
struct Witness
{
    BigInt l;
    size_t Ran_num;
    std::vector<BigInt> randoms;
};
// define structure of ManyOutOfManyProof
struct Proof
{
    ECPoint proof_A, proof_B ,proof_C, proof_D;
    std::vector<ECPoint> vec_Gk;
    std::vector<BigInt> vec_proof_f;
    BigInt proof_Za, proof_Zc, proof_z;
 
};
PP Setup(size_t Com_LEN, size_t o,std::vector<std::vector<BigInt> >vec_xi)
{
    PP pp;
    pp.Com_LEN = Com_LEN;
    pp.Log_Com_Len = size_t(log2(Com_LEN));
    pp.com_part = Pedersen::Setup(pp.Log_Com_Len);
    pp.o = o;
    pp.vec_xi = vec_xi;
    return pp;

}

ECPoint Commit2(const BigInt &x, const BigInt &y,  const Ck &ck)
{
    return ck.gk * x + ck.hk * y;
}

BigInt Accumulate(std::vector<BigInt> vec,const BigInt &mod)
{
    BigInt ans=BigInt(bn_1);
    for(auto i=0;i<vec.size();i++)
    {
        ans=(ans*vec[i])%mod;
    }
    return ans;
}
std::vector<BigInt> BigIntPolModProduct(std::vector< std::vector<std::pair<BigInt, BigInt>> >vec_F,BigInt index, BigInt mod)
{
    size_t k=vec_F.size(); // n is the number of rows, m is the number of columns,m=2;
    size_t m=vec_F[0].size();
    std::vector<BigInt> vec_ans(k+1,bn_0);
    size_t n=1<<k;//n=2^k;
    size_t sum=0;
    std::vector<BigInt> vec_tmp(k);
    //std::cout<<"n="<<n<<std::endl;
    //std::cout<<"k="<<k<<std::endl;
    for(auto i=0;i<n;i++)
    {
        for(auto j=0;j<k;j++)
        {
            if(((i>>j)&1)==1)
            {
                sum++;
                vec_tmp[j]=vec_F[j][index.GetTheNthBit(j)].first;
            }
            else
            {
                vec_tmp[j]=vec_F[j][index.GetTheNthBit(j)].second;
            }

        }
        BigInt tmp_acc=Accumulate(vec_tmp,mod);
        vec_ans[sum]=(vec_ans[sum]+tmp_acc)%mod;
        sum=0;      
    }
    return vec_ans;
}
/* generate a^n = (a^0, a^1, a^2, ..., a^{n-1}) */ 
std::vector<BigInt> GenBigIntPowerVector(size_t LEN, const BigInt &a)
{
    
    std::vector<BigInt> vec_result(LEN);
    vec_result[0] = BigInt(bn_1); 
    for (auto i = 1; i < LEN; i++)
    {
        vec_result[i] = (vec_result[i-1] * a) % order; // result[i] = result[i-1]*a % order
    }
    return vec_result; 
}
std::vector<BigInt> GenBigIntmatrixProduct(std::vector<BigInt> vec_a,std::vector<std::vector<BigInt> >vec_b,const BigInt &mod)
{
    size_t n=vec_a.size();
    size_t m=vec_b.size();
    size_t k=vec_b[0].size();
    std::vector<BigInt> vec_ans(k);
    BigInt tmp=bn_0;
    for(auto i=0;i<k;i++)
    {
        tmp=bn_0;
        for(auto j=0;j<m;j++)
        {            
            tmp=(tmp+vec_a[j]*vec_b[j][i])%mod;
        }
        vec_ans[i]=tmp%mod;
    }
    return vec_ans;
}
void Prove(PP &pp,Witness &witness,Instance &instance,std::string &transcript_str, Proof &proof,const Ck &ck)
{
    
    BigInt ra = GenRandomBigIntLessThan(order); 
    BigInt rb = GenRandomBigIntLessThan(order);
    BigInt rc = GenRandomBigIntLessThan(order);
    BigInt rd = GenRandomBigIntLessThan(order);
    size_t n=pp.Com_LEN;
    size_t m=pp.Log_Com_Len;
    std::vector<BigInt> al(m);
    std::vector<BigInt> bl(m);
    BigInt l=witness.l;
    
    for(auto i=0; i<m; i++)
    {
        al[i]=GenRandomBigIntLessThan(order);
        if(l.GetTheNthBit(i)==1)   //need to be modified
        {
            bl[i]=bn_1;
        }
        else
        {
            bl[i]=bn_0;
        }    
    }
   
    std::vector<BigInt> vec_ma(m);
    std::vector<BigInt> vec_mb(m);
    std::vector<BigInt> vec_mc(m);
    std::vector<BigInt> vec_md(m);

    /*fill vec_ma and vec_mb*/
    std::copy(al.begin(), al.end(), vec_ma.begin());
    std::copy(bl.begin(), bl.end(), vec_mb.begin());

    /*fill vec_mc*/
     std::vector<BigInt> vec_tmpb(m);
    BigInt bk2=bn_2.Negate();
    std::vector<BigInt> bn1(m,bn_1);
    vec_tmpb=BigIntVectorModScalar(bl, bk2, order);
 
    vec_tmpb=BigIntVectorModAdd(vec_tmpb, bn1, order);
    vec_tmpb=BigIntVectorModProduct(vec_tmpb, al, order);
    std::copy(vec_tmpb.begin(), vec_tmpb.end(), vec_mc.begin());
    
    /*fill vec_md*/
    std::vector<BigInt> vec_tmpa(m);
    BigInt modx=order;
    vec_tmpa=BigIntVectorModNegate(al,modx);
  
    vec_tmpa=BigIntVectorModProduct(vec_tmpa, al, order);
    std::copy(vec_tmpa.begin(), vec_tmpa.end(), vec_md.begin());
    
    proof.proof_A=Pedersen::Commit(pp.com_part, vec_ma, ra); //comiitment of A

    proof.proof_B=Pedersen::Commit(pp.com_part, vec_mb, rb); //commitment of B
    proof.proof_C=Pedersen::Commit(pp.com_part, vec_mc, rc); //commitment of C
    proof.proof_D=Pedersen::Commit(pp.com_part, vec_md, rd); //commitment of D

    std::vector< std::vector< std::pair<BigInt, BigInt>> > vec_F(m,std::vector<std::pair<BigInt, BigInt>>(2)); 
    std::vector< std::vector<BigInt> > vec_P(n,std::vector<BigInt>(m)); //n rows ,m columns

    /*compute F and P*/
    for(auto k=0;k<m;k++)
    {   
        std::pair<BigInt, BigInt> tmp;
        tmp.first=bl[k];
        tmp.second=al[k];
        vec_F[k][1]=tmp;
        tmp.first=(bn_1-bl[k]);
        tmp.second=-al[k];
        vec_F[k][0]=tmp;
    }
    std::vector<BigInt> vec_product_tmp;
    for(auto i=0;i<n;i++)
    {
        vec_product_tmp=BigIntPolModProduct(vec_F,i, order);
        vec_P[i]=vec_product_tmp;             
    }
    /*test*/
    /*std::vector<BigInt> vec_test(2);
    std::vector<BigInt> vec_test2(2);
    std::vector<std::vector<BigInt> > vec_test3(n);
    for(auto i=0;i<n;i++)
    {
        BigInt index=BigInt(i);
        vec_test.clear();
        vec_test.push_back(vec_F[0][index.GetTheNthBit(0)].second);
        vec_test.push_back(vec_F[0][index.GetTheNthBit(0)].first);
        for(auto j=1;j<m;j++)
        {
            index=BigInt(i);
            vec_test2[0]=vec_F[j][index.GetTheNthBit(j)].second;
            vec_test2[1]=vec_F[j][index.GetTheNthBit(j)].first;
            vec_test=PolyMul(vec_test, vec_test2);
        }
        vec_test3[i]=vec_test;
    }

    for(auto i=0;i<n;i++)
    {
        for(auto k=0;k<=m;k++)
        {
            if(vec_test3[i][k]!=vec_P[i][k])
            {
                std::cout<<"error"<<std::endl;
                vec_test3[i][k].Print("vec_test3");
                vec_P[i][k].Print("vec_P");
            }
            
        }
    }*/

    /*compute challenge v*/
    transcript_str+=proof.proof_A.ToByteString();
    transcript_str+=proof.proof_B.ToByteString();
    transcript_str+=proof.proof_C.ToByteString();
    transcript_str+=proof.proof_D.ToByteString();

    BigInt v=Hash::StringToBigInt(transcript_str);

    
    /*compute  Gk*/
    size_t rs=witness.Ran_num;
   
    std::vector<BigInt> vec_v=GenBigIntPowerVector(rs, v);

    /*compute \xi*/
    
    std::vector<BigInt> vec_ksi=GenBigIntmatrixProduct(vec_v, pp.vec_xi, order);

    size_t o=vec_ksi.size();
    
    proof.vec_Gk.resize(m);
    std::vector<BigInt> vec_pktmp(n);
    std::vector<ECPoint> vec_comtmp(o);      
    std::vector<BigInt> vec_rho(m);   
    vec_rho=GenRandomBigIntVectorLessThan(m,order);   
    ECPoint Ec_tmp;
    transcript_str=""; 
    BigInt rhotmp;                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               
    for(auto k=0;k<m;k++)
    {
        for(auto j=0;j<o;j++)
        {
            for(auto i=0;i<n;i++)
            {
                size_t index_ka=(i-2*j+n)%n;
                vec_pktmp[i]=vec_P[index_ka][k];
            } 
            vec_comtmp[j]=ECPointVectorMul(instance.vec_com, vec_pktmp);
        }
        proof.vec_Gk[k]=ECPointVectorMul(vec_comtmp, vec_ksi);
        rhotmp=vec_rho[k];
        Ec_tmp=Commit2(bn_0,rhotmp,ck);
        proof.vec_Gk[k]=proof.vec_Gk[k]+Ec_tmp;
        transcript_str+=proof.vec_Gk[k].ToByteString();
    }

    /*test*/
    /*std::vector<ECPoint> vec_test4(m);
    for(auto k=0;k<m;k++)
    {
        ECPoint Ec_tmp22;
        for(auto j=0;j<o;j++)
        {
            ECPoint Ec_tmp2;
            for(auto i=0;i<n;i++)
            {
                size_t index_ka=(i-2*j+n)%n;
                vec_pktmp[i]=vec_P[index_ka][k];
                if(i==0)
                {
                    Ec_tmp2=instance.vec_com[i]*vec_pktmp[i];
                }
                else
                {
                    Ec_tmp2+=instance.vec_com[i]*vec_pktmp[i];
                }
                
            } 
            if(j==0)
            {
                Ec_tmp22=Ec_tmp2*vec_ksi[j];
            }
            else
            {
                Ec_tmp22+=Ec_tmp2*vec_ksi[j];
            }
            
        }
       
        vec_test4[k]=Ec_tmp22;
        rhotmp=vec_rho[k];
        Ec_tmp=Commit2(bn_0,rhotmp,ck);
        vec_test4[k]=vec_test4[k]+Ec_tmp;
        if(vec_test4[k]!=proof.vec_Gk[k])
        {
            std::cout<<"error"<<std::endl;
            vec_test4[k].Print("vec_test4");
            proof.vec_Gk[k].Print("proof.vec_Gk");
        }
    }*/

    
    /*compute challenge x*/
    BigInt x=Hash::StringToBigInt(transcript_str);
    x.Print("xp");
    /*compute f,za,zc,z*/
    proof.vec_proof_f.resize(m);
    for(auto k=0;k<m;k++)
    {
        proof.vec_proof_f[k]=(bl[k]*x%order+al[k])%order;
        
    }
    proof.proof_Za=(rb*x%order+ra)%order;
    proof.proof_Zc=(rc*x%order+rd)%order;

    BigInt sum_v=bn_0;
    BigInt sum_tmp1;
    for(auto i=0;i<rs;i++)
    {
        sum_tmp1=vec_v[i]*witness.randoms[i]%order;
        sum_v=(sum_v+ sum_tmp1)%order;
    }
    
    BigInt Bm=BigInt(m);
    
    BigInt xexpm=x.ModExp(Bm,order);
    
    BigInt sum_rho=bn_0;
    BigInt sum_tmp2;
    for(auto i=0;i<m;i++)
    {
        BigInt BI=BigInt(i);
        sum_tmp2=(vec_rho[i]*x.ModExp(BI,order))%order;
        sum_rho=(sum_rho+sum_tmp2)%order;
        
    }
    
    proof.proof_z=(sum_v*xexpm-sum_rho)%order;
    
    //proof.proof_z.Print("proof.proof_z");

    #ifdef DEBUG
        std::cout << "Many prove Succeeds >>>" << std::endl; 
    #endif
    
    
}

bool Verify(PP &pp, Instance &instance, std::string &transcript_str, Proof &proof,Ck &ck)
{
    
    transcript_str+=proof.proof_A.ToByteString();
    transcript_str+=proof.proof_B.ToByteString();
    transcript_str+=proof.proof_C.ToByteString();
    transcript_str+=proof.proof_D.ToByteString();

    BigInt v=Hash::StringToBigInt(transcript_str);

    size_t rs=pp.vec_xi.size();
    std::vector<BigInt> vec_v=GenBigIntPowerVector(rs, v);
    /*compute \xi*/
    //std::vector<BigInt> vec_vsi(o);
    std::vector<BigInt> vec_ksi=GenBigIntmatrixProduct(vec_v, pp.vec_xi, order);

    size_t o=vec_ksi.size();
    size_t m=proof.vec_Gk.size();

    transcript_str="";
    for(auto k=0;k<m;k++)
    {
        transcript_str+=proof.vec_Gk[k].ToByteString();
    }

    BigInt x=Hash::StringToBigInt(transcript_str);

    x.Print("xv");

    //wrong here
    /*std::vector<BigInt> vec_ftmp(m);
    BigInt bn11=-bn_1;
    std::vector<BigInt> vec_x(m,x);
    vec_ftmp=BigIntVectorModScalar(proof.vec_proof_f, bn11,order);
    vec_ftmp=BigIntVectorModAdd(vec_x, vec_ftmp,order);
    vec_ftmp=BigIntVectorModProduct(vec_ftmp, proof.vec_proof_f,order);*/

    std::vector<BigInt> vec_ftmp2(m);
    for(auto i=0;i<m;i++)
    {
        vec_ftmp2[i]=proof.vec_proof_f[i]*((x-proof.vec_proof_f[i]+order)%order)%order;
    }

    
    /*check B^x*A and C^X*D*/
    ECPoint EC_A=Pedersen::Commit(pp.com_part,proof.vec_proof_f,proof.proof_Za);
    ECPoint EC_B=Pedersen::Commit(pp.com_part,vec_ftmp2,proof.proof_Zc);

    ECPoint EC_BXA=proof.proof_B*x+proof.proof_A;
    ECPoint EC_CXD=proof.proof_C*x+proof.proof_D;
    
    
    if(EC_BXA!=EC_A||EC_CXD!=EC_B)
    {
        return false;
    }

    /*check Gk*/
    size_t n=pp.Com_LEN;
    std::vector<BigInt> vec_p(n);
    BigInt mul_tmp;
    BigInt indextmp;
    for(auto i=0;i<n;i++)
    {
        mul_tmp=bn_1;
        for(auto k=0;k<m;k++)
        {
            indextmp=BigInt(i);
            if(indextmp.GetTheNthBit(k)==1)
            {
                mul_tmp=mul_tmp*proof.vec_proof_f[k]%order;
            }
            else
            {
                mul_tmp=mul_tmp*(x-proof.vec_proof_f[k])%order; 
            }
        }
        vec_p[i]= mul_tmp%order;
    }

    /* mul exp check*/
    std::vector<BigInt> vec_ptmp(n);
    std::vector<ECPoint> vec_comtmp(o);
    for(auto j=0;j<o;j++)
    {
        for(auto i=0;i<n;i++)
        {
            size_t index_ka=(i-2*j+n)%n;
            vec_ptmp[i]=vec_p[index_ka];
        } 
        vec_comtmp[j]=ECPointVectorMul(instance.vec_com, vec_ptmp);
    }
    ECPoint EC_GK=ECPointVectorMul(vec_comtmp, vec_ksi);
   
    std::vector<BigInt> vec_xk(m);
    vec_xk=GenBigIntPowerVector(m, x);

    BigInt bk111=-bn_1;
    vec_xk=BigIntVectorModScalar(vec_xk,bk111,order);

    /*replace 
    vec_xk=BigIntVectorModScalar(vec_xk,-1,order);
    */
    std::vector<BigInt> vec_xk2(m);
    vec_xk2=GenBigIntPowerVector(m,x);
    ECPoint EC_GK2=ECPointVectorMul(proof.vec_Gk, vec_xk);

    ECPoint EC_z=Commit2(bn_0,proof.proof_z,ck);
      
    bool Validity =true;     
    
    if(EC_z!=(EC_GK+EC_GK2))
    {
        Validity=false; 
        std::cout<<"EC_z!=(EC_GK+EC_GK2)"<<std::endl;      
    }
  
    #ifdef DEBUG
    if (Validity){ 
        std::cout<< " accepts >>>" << std::endl; 
    }
    else{
        std::cout<< " rejects >>>" << std::endl; 
    }
    return Validity;
    #endif



}

}
#endif