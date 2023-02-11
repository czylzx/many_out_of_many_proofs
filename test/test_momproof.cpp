#define DEBUG

#include "../zether/many_out_of_many/many_out_of_many.hpp"
#include "../crypto/setup.hpp"


/*void test_accountable_ring_sig()
{
    PrintSplitLine('-');  
    std::cout << "begin the test of many_out_of_many.hpp >>>" << std::endl; 

    AccountableRingSig::PP pp; 
    AccountableRingSig::SP sp;
    size_t N_max = 32; 
    std::tie(pp, sp) = AccountableRingSig::Setup(N_max); 

    size_t N = 8; // ring size
    std::vector<ECPoint> vk_ring(N);
    std::vector<BigInt> sk_ring(N); 
    for(auto i = 0; i < N; i++){
        std::tie(vk_ring[i], sk_ring[i]) = AccountableRingSig::KeyGen(pp); 
    }
    srand(time(0));
    size_t index = rand() % N; 

    std::string message = "I am a hacker"; 
    AccountableRingSig::Signature sigma; 
    auto start_time = std::chrono::steady_clock::now(); // start to count the time
    sigma = AccountableRingSig::Sign(pp, sk_ring[index], vk_ring, message);
    auto end_time = std::chrono::steady_clock::now(); // end to count the time
    auto running_time = end_time - start_time;
    std::cout << "size-" << N << " acountable ring signature generation takes time = " 
    << std::chrono::duration <double, std::milli> (running_time).count() << " ms" << std::endl;

    start_time = std::chrono::steady_clock::now(); // start to count the time
    AccountableRingSig::Verify(pp, vk_ring, message, sigma);
    end_time = std::chrono::steady_clock::now(); // end to count the time
    running_time = end_time - start_time;
    std::cout << "size-" << N << " acountable ring signature verification takes time = " 
    << std::chrono::duration <double, std::milli> (running_time).count() << " ms" << std::endl;

    start_time = std::chrono::steady_clock::now(); // start to count the time
    DLOGEquality::Proof correct_decryption_proof;
    ECPoint vk; 
    std::tie(vk, correct_decryption_proof) = AccountableRingSig::Open(pp, sp, vk_ring, sigma);
    end_time = std::chrono::steady_clock::now(); // end to count the time
    running_time = end_time - start_time;
    std::cout << "size-" << N << " acountable ring signature open takes time = " 
    << std::chrono::duration <double, std::milli> (running_time).count() << " ms" << std::endl;

    start_time = std::chrono::steady_clock::now(); // start to count the time
    AccountableRingSig::Justify(pp, vk_ring, sigma, vk, correct_decryption_proof);
    end_time = std::chrono::steady_clock::now(); // end to count the time
    running_time = end_time - start_time;
    std::cout << "size-" << N << " acountable ring signature justify takes time = " 
    << std::chrono::duration <double, std::milli> (running_time).count() << " ms" << std::endl;

}*/
ECPoint Commit2(const BigInt& r, const BigInt& m, const ECPoint& g, const ECPoint& h)
{
    return g * r + h * m;
}
void test_many_out_of_many(size_t N_max,size_t o,size_t Rs,std::vector<std::vector<BigInt> >vec_xi,size_t index)
{
    PrintSplitLine('-');  
    std::cout << "begin the test of many_out_of_many.hpp >>>" << std::endl; 

    ManyOutOfMany::PP pp;
    ManyOutOfMany::Ck ck;
    ManyOutOfMany::Instance instance;
    ManyOutOfMany::Witness witness;
    ManyOutOfMany::Proof proof;

    pp=ManyOutOfMany::Setup(N_max,o,vec_xi);
    
    //ck.gk = generator; 
    ck.gk=GenRandomGenerator();
    ck.hk=GenRandomGenerator();
    //ck.hk = Hash::StringToECPoint(ck.gk.ToByteString()); 

    witness.l=index;
    witness.Ran_num=Rs;
    witness.randoms.resize(Rs);
    witness.randoms=GenRandomBigIntVectorLessThan(Rs,order);


    instance.Com_Num = N_max;
    instance.vec_com.resize(N_max);
    std::vector<ECPoint> commitments(N_max);
    std::vector<size_t> indexs(N_max,0);
    for(auto i=0;i<o;i++)
    {
        for(auto j=0;j<Rs;j++)
        {
            size_t indexnew=(index+2*j)%N_max;
            commitments[indexnew]=Commit2(bn_0,witness.randoms[j],ck.gk,ck.hk);
            indexs[indexnew]=1;
        }
    }
    for(auto i=0;i<N_max;i++)
    {
        if(indexs[i]==0)
        {
            BigInt ran1=GenRandomBigIntLessThan(order);
            BigInt ran2=GenRandomBigIntLessThan(order);
            commitments[i]=Commit2(ran1,ran2,ck.gk,ck.hk);
        }
    }
    /*wrong here*/
    /*if(index%2==0)
    {
        for(auto i = 0; i < N_max; i++){
            BigInt ran1=GenRandomBigIntLessThan(order);
            BigInt ran2=GenRandomBigIntLessThan(order);
            //commitments[i] = Commit2(bn_0,witness.randoms[i/2], ck.gk, ck.hk);
            if(i%2==0)
            commitments[i] = Commit2(bn_0, witness.randoms[i/2],ck.gk, ck.hk);
            else
            commitments[i] = Commit2(ran1, ran2, ck.gk, ck.hk);
        }
    }
    else
    {
        for(auto i = 0; i < N_max; i++){
            BigInt ran1=GenRandomBigIntLessThan(order);
            BigInt ran2=GenRandomBigIntLessThan(order);
            if(i%2==1)
            commitments[i] = Commit2(bn_0, witness.randoms[i/2+1], ck.gk, ck.hk);
            else
            commitments[i] = Commit2(ran1, ran2, ck.gk, ck.hk);
        }  
    }*/
    instance.vec_com=commitments;
    //instance.vec_com[index].Print("commitments[index]");
    std::string message = "";
    ManyOutOfMany::Prove(pp, witness, instance,message, proof,ck);
    
    message = "";
    bool testval=ManyOutOfMany::Verify(pp, instance, message, proof,ck);
    
    if(testval==true)
    {
        std::cout<<"verify success"<<std::endl;
    }
    else
    {
        std::cout<<"verify fail"<<std::endl;
    }


    //pp.u = GenRandomGenerator();
    /*AccountableRingSig::PP pp; 
    AccountableRingSig::SP sp;
    size_t N_max = 32; 
    std::tie(pp, sp) = AccountableRingSig::Setup(N_max); 

    size_t N = 8; // ring size
    std::vector<ECPoint> vk_ring(N);
    std::vector<BigInt> sk_ring(N); */

}
int main()
{
    CRYPTO_Initialize(); 
    size_t N_max = 8;
    size_t o=N_max/2;
    size_t Rs=N_max/2;

    std::vector<std::vector<BigInt> > vec_xi(Rs, std::vector<BigInt>(o));

    for(auto i = 0; i < Rs; i++){
        for(auto j = 0; j < o; j++){
            if(i==j)
                vec_xi[i][j] = bn_1;
            else
                vec_xi[i][j] = bn_0;
        }
    }
    
    size_t index=2;
    test_many_out_of_many(N_max, o, Rs, vec_xi,index);

    CRYPTO_Finalize(); 

    return 0; 
}



