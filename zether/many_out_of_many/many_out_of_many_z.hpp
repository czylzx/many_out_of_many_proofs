/***********************************************************************************
this hpp implements many_out_of_many proof for Anonymous Zether  
***********************************************************************************/
#ifndef MANY_OUT_OF_MANY_HPP_
#define MANY_OUT_OF_MANY_HPP_
#include "../zkp/nizk/nizk_enc_relation.hpp"
#include "../zkp/nizk/nizk_dlog_equality.hpp"
#include <utility>
//#include "innerproduct_proof.hpp" 

namespace ManyOutOfMany{
// define structure of ManyOutOfManyProof
struct PP
{
    Pedersen::PP com_A;
    Pedersen::PP com_B;
    size_t Com_LEN;
    size_t Log_Com_Len;
    //Pedersen::PP com_part;
    //TwistedElGamal::PP enc_part;
    ECPoint ek;
};
struct Instance
{
    std::vector<BigInt> s, t;
    BigInt r;
    ECPoint vk;
};
struct Witness
{
    BigInt l0;
    BigInt l1;
    BigInt rb;
    std::vector<BigInt> randoms;
};
// define structure of ManyOutOfManyProof
struct Proof
{
    ECPoint proof_A, proof_B;
    EncRelation::Proof correct_encryption_proof;
    BigInt z_s, z_t;
    TwistedElGamal::CT ct_vk, ct_s;
};
struct SP
{
    BigInt dk;
};

// structure of keypair
struct KeyPair
{
    ECPoint vk;
    BigInt sk;
};

/* Setup algorithm */
std::tuple<PP, SP> Setup(size_t N_max)
{
    PP pp;
    SP sp;
    pp.com_A = Pedersen::Setup(N_max); // commitment set up
    pp.com_B = Pedersen::Setup(N_max);

    size_t MSG_LEN = 32;
    size_t TRADEOFF_NUM = 7;
    size_t DEC_THREAD_NUM = 8;
    pp.enc_part = TwistedElGamal::Setup(MSG_LEN, TRADEOFF_NUM);

    std::tie(pp.ek, sp.dk) = TwistedElGamal::KeyGen(pp.enc_part);
    return {pp, sp};
}
BigInt Accumulate(std::vector<BigInt> vec,const BigInt &mod)
{
    BigInt ans=0;
    for(auto i=0;i<vec.size();i++)
    {
        ans=(ans+vec[i])%mod;
    }
    return ans;
}
std::vector<BigInt> BigIntMatrixtModProduct(std::vecotr< std::vector<std::pair<BigInt, BigInt> > > vec_F,size_t index,const BigInt &mod)
{
    size_t k=vec_F.size(); // n is the number of rows, m is the number of columns,m=2;
    size_t m=vec_F[0].size();
    std::vector<BigInt> vec_ans(k,0);
    size_t n=1<<k;//n=2^k;
    size_t sum=0;
    std::vector<BigInt> vec_tmp(k);
    for(auto i=0;i<n;i++)
    {
        for(auto j=0;j<m;j++)
        {
            if((i>>j)&1==1)
            {
                sum++;
                vec_tmp[j]=vec_F[j][i.GetTheNthBit(j)].first;
            }
            else
            {
                vec_tmp[j]=vec_F[j][i.GetTheNthBit(j)].second;
            }

        }
        BigInt tmp_acc=Accumulate(vec_tmp,mod);
        vec_ans[sum]+=tmp_acc;
        sum=0;      
    }
    return vec_ans;
}
{

}
void Prove(PP &pp)
{
    BigInt ra = GenRandomBigIntLessThan(order); 
    BigInt rb = GenRandomBigIntLessThan(order);
    size_t n=pp.Com_LEN;
    siez_t m=pp.Log_Com_LEN;
    std::vector<BigInt> al1(m);
    std::vector<BigInt> al0(m);
    std::vector<BigInt> bl1(m);
    std::vector<BigInt> bl0(m);
    for(auto i=0; i<m; i++)
    {
        al1[i]=GenRandomBigIntLessThan(order);
        al0[i]=GenRandomBigIntLessThan(order);
        if(l0.GetTheNthBit(i)==1)   //need to be modified
        {
            bl0[i]=bn_1;
        }
        else
        {
            bl0[i]=bn_0;
        }
        if(l1.GetTheNthBit(i)==1)
        {
            bl1[i]=bn_1;
        }
        else
        {
            bl1[i]=bn_0;
        }
    }
    std::vector<BigInt> vec_ma(4*m+2);
    std::vector<BigInt> vec_mb(4*m+2);
    /*fill vec_ma*/
    /*0- 2m-1*/
    std::copy(al0.begin(), al0.end(), vec_ma.begin());
    std::copy(al1.begin(), al1.end(), vec_ma.begin()+m);
    /*2m - 3m-1*/
    std::vector<BigInt> vec_tmpa(m);
    vec_tmpa=BigIntVectorModNegate(al0, -1, order);
    vec_tmpa=BigIntVectorModProduct(vec_tmpa, al0, order);
    std::copy(vec_tmpa.begin(), vec_tmpa.end(), vec_ma.begin()+2*m);
    /*3m - 4m-1*/
    vec_tmpa=BigIntVectorModNegate(al1 ,-1, order);
    vec_tmpa=BigIntVectorModProduct(vec_tmpa, al1, order);
    std::copy(vec_tmpa.begin(), vec_tmpa.end(), vec_mb.begin()+3*m);
    /*4m and 4m+1*/
    vec_ma[4*m]=((al0[0]*al1[0])%order);
    vec_ma[4*m+1]=vec_ma[4*m];

    /*fill vec_mb*/
    /*0- 2m-1*/
    std::copy(bl0.begin(), bl0.end(), vec_mb.begin());
    std::copy(bl1.begin(), bl1.end(), vec_mb.begin()+m);
    /*2m - 3m-1*/
    std::vector<BigInt> vec_tmpb(m);
    vec_tmpb=BigIntVectorModNegate(bl0, -2, order);
    vec_tmpb=BigIntVectorModAdd(vec_tmpb, 1, order);
    vec_tmpb=BigIntVectorModProduct(vec_tmpb, al0, order);
    std::copy(vec_tmpb.begin(), vec_tmpb.end(), vec_mb.begin()+2*m);
    /*3m - 4m-1*/
    vec_tmpb=BigIntVectorModNegate(bl1 ,-2, order);
    vec_tmpb=BigIntVectorModAdd(vec_tmpb, 1, order);
    vec_tmpb=BigIntVectorModProduct(vec_tmpb, al1, order);
    std::copy(vec_tmpb.begin(), vec_tmpb.end(), vec_mb.begin()+3*m);
    /*4m and 4m+1*/
    if(bl0[0]==bn_1 && bl1[0]==bn_1)    //need to be modified, modifie vectore to Two-dimensional vector
    {
        vec_mb[4*m]=(al1[0]%order);
        vec_mb[4*m+1]=(-1*al0[0]%order);
    }
    else if(bl0[0]==bn_1 && bl1[0]==bn_0)
    {
        vec_mb[4*m]=(al1[0]%order);
        vec_mb[4*m+1]=(-1*al0[0]%order);
    }
    else if(bl0[0]==bn_0 && bl1[0]==bn_1)
    {
        vec_mb[4*m]=(al0[0]%order);
        vec_mb[4*m+1]=(-1*al1[0]%order);
    }
    else
    {
        vec_mb[4*m]=(al0[0]%order);
        vec_mb[4*m+1]=(-1*al0[0]%order);
    }
    proof_A=Pedersen::Commit(pp.com_A, vec_ma, ra); //comiitment of A
    proof_B=Pedersen::Commit(pp.com_B, vec_mb, rb); //commitment of B

    std::vecotr< std::vector<std::pair<BigInt, BigInt> > > vec_F0(m,vector<std::pair<BigInt, BigInt>(2)); //subscript 0 means l0, subscript 1 means l1
    std::vecotr< std::pair<BigInt, std::pair<BigInt, BigInt> > > vec_F1(m);
    std::vector< std::vector<BigInt> > vec_P0(n,vector<BigInt>(m)); //n rows ,m columns
    std::vector< std::vector<BigInt> > vec_P1(n,vector<BigInt>(m));
    /*compute Flk1 and Flk0*/
    for(auto l=0; l<2; l++)
    {
        for(auto k=0;k<m;k++)
        {
            if(l==0)
            {
                std::pair<BigInt, BigInt> > tmp;
                tmp.first=bl0[k];
                tmp.second=al0[k];
                vec_F0[k][1]=tmp;
                tmp.first=(1-bl0[k]);
                tmp.second=-al0[k];
                vec_F0[k][0]=tmp;
            }
            else
            {
                //std::pair<BigInt, BigInt> > tmp;
                tmp.first=bl1[k];
                tmp.second=al1[k];
                vec_F1[k][1]=tmp;
                tmp.first=(1-bl1[k]);
                tmp.second=-al1[k];
                vec_F1[k][0]=tmp;
                
            }
        }
        std::vector<BigInt> vec_product_tmp0;
        std::vector<BigInt> vec_product_tmp1;
        for(auto i=0;i<n;i++)
        {
            vec_product_tmp0=BigIntMatrixtModProduct(vec_F0,i, order);
            vec_P0[i]=vec_product_tmp0;              
            vec_product_tmp1=BigIntMatrixtModProduct(vec_F1,i, order);
            vec_P1[i]=vec_product_tmp1;                              
            

        }
    }
    

}

}
#endif