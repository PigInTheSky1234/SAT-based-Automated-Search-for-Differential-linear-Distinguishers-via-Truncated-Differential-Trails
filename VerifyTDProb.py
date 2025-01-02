import numpy as np
import math as mt

def RorL(x,l,n=8):
    MASK=2**n -1
    return  ((x<<l) |(x>>(n-l)))&MASK



def SimonFuc(x,n=8,a=7,b=4):
    MASK = 2 ** n - 1

    return (RorL(x,a,n)&RorL(x,b,n))  &MASK

def genTD(X,n):
    TD=[]
    TempX = X
    MaskX=0
    IndexX=[]


    for i in range(n):
        TD.append(TempX%3)
        MaskX=MaskX<<1
        if (TempX%3)<2:
            MaskX|=TempX%3
        else:
            IndexX.append(n-1-i)

        TempX=TempX//3
    return TD,MaskX,IndexX



def genTD2(X,n):
    TD=[]
    TempX = X
    MaskX=0
    Mask2=0


    for i in range(n):
        TD.append(TempX%3)
        MaskX=MaskX<<1
        Mask2 = Mask2<<1
        if (TempX%3)<2:
            MaskX|=1
            Mask2|=TempX%3


        TempX=TempX//3
    return TD,MaskX,Mask2


def CheckDiff(dx,dy,a,b,n):
    for i in range(n):
        if ( (dx[(i+a)%n]==2)| (dx[(i+b)%n]==2)) & (dy[i]<=1):
            return False
    return True


def GenInDiffs(Mdx,Indexdx,n):
    InDiffs=[]
    NumAsterisk=len(Indexdx)
    for i in range(2**NumAsterisk):
        Tempx=0
        for j in range(NumAsterisk):
            if (i>>j)&1:
                Tempx|=1<<Indexdx[j]


        InDiffs.append(Tempx|Mdx)
    return InDiffs








def TESTProb(dx,Maskdy,dy,n,a,b):
    """
    statistic the prob. when the input diff. is fixed and the output difference is truncated
    :param dx:
    :param dy:
    :param n:
    :return:
    """

    X1=np.arange(2**n)

    X1=np.array(X1,dtype=np.uint)
    X2=X1^dx


    Y1 = SimonFuc(X1, n=n, a=a, b=b)
    Y2 = SimonFuc(X2 , n=n, a=a, b=b)

    Counter = np.sum( ((Y1^Y2)&Maskdy)==dy)

    # print(Maskdy,dy)
    #
    # print(Y1^Y2)
    # print(X1,X2)
    # print("**********************")
    # print(Y1,Y2)
    #
    # print(X1)
    # print(RorL(X1, a, n))

    return Counter/(2**n)

def VerfyProb(InDiffs,Maskdy,OutDiff,n,a,b):
    SumProb=0
    #print(InDiffs)
    NumIn=len(InDiffs)
    #print(InDiffs)
    for InD in InDiffs:
        #print(InD,OutMask,n,a,b)
        TempProb=TESTProb(InD,Maskdy,OutDiff,n,a,b)
        #print(TempProb)
        SumProb+=TempProb
    return SumProb/NumIn


wt=[]
for i in range(2**8):
    Counter=0
    for j in range(8):
        if (i>>j)&1:
            Counter+=1

    wt.append(Counter)


def CalculateProb(Vardx, Vardy, n, a, b):
    Flag=True

    for i in range(n):
        if Vardx[i]!=1:
            Flag=False
            break


    #1. Input diff. is all 1s

    if Flag:
        Counter=0
        Counter2=0
        for i in range(n):
            if Vardy[i] == 2:
                Counter+=1
            if Vardy[i] == 1:
                Counter2+=1
        if Counter==0:
            if Counter2&1:
                return 0,0,0
            else:
                return 2**(-n+1),0,0
        else:
            return 2 **( Counter-n ),0,0

    else:
        v=0
        d=0
        for i in range(n):
            if Vardy[i]!=2:
                v|= (Vardx[(i+a ) %n]| Vardx[(i+b)%n])<<(n-1-i)
                #print(hex(v),i)

            if (Vardy[i] != 2)&(Vardy[(i+a-b ) %n]!=2) :# &(Vardx[(i+2*a-b ) %n]!=2)
                #print(i,Vardy[i],Vardy[(i+a ) %n],Vardx[(i+2*a-b ) %n],"Error")
                d|=(Vardx[(i+b ) %n] &( 1-Vardx[(i+a ) %n]  ) & Vardx[(i+2*a-b ) %n] )<<(n-1-i)
                #print(bin(d))

        for i in range(n):
            if (1-(v>>i)&1 )& (Vardy[-1-i]==1):
                return 0,v,d

            if ( (d >> i) & 1) &   (  ((Vardy[-1 - i]  +  Vardy[(-1 - i+a-b)%n])&1)!=0 ):
                #print(i,"Error")
                return 0,v,d


        return  2**(-wt[v^d]),v,d



if __name__=="__main__":
    TestProb=True

    ComputeProb=False

    if TestProb:
        n=8
        a=7
        b=4

        NotSolved=[]
        DDT=[]
        Completed=-1
        for dx in range(3**n):
            if (dx//(3**(n-3)) )!=Completed:
                Completed=(dx//(3**(n-3)) )
                print("Completed ", Completed /(3**3)*100,"   %")

            for dy in range(3**n):

                Vardx,Mdx,Indexdx =genTD(dx,n)
                Vardy,Maskdy,OutDiff = genTD2(dy, n)


                if not CheckDiff(Vardx,Vardy,a,b,n):

                    NotSolved.append([Vardx,Vardy,dx,dy])
                    continue

                InDiffs=GenInDiffs(Mdx, Indexdx, n)

                P1=VerfyProb(InDiffs, Maskdy,OutDiff, n, a, b)

                P2,v,d=CalculateProb(Vardx, Vardy, n, a, b)

                Temp=[Vardx,Mdx,Indexdx,
                      Vardy, Maskdy,OutDiff,
                      P1,P2

                      ]
                #print(Temp)
                DDT.append(Temp)
                if P1!=P2:
                    print("Error",Temp,hex(Maskdy),hex(OutDiff),"{:08b}".format(v),"{:08b}".format(d))
                # else:
                #     print(Temp)
        print("Verify completed.")
        print(DDT)

    if ComputeProb:
        n = 8
        a = 7
        b = 4

        InDiffs=[0b10100000,
                #0b00100000,

                 ]
        OutDiff=0x4

        Vardx=[1,0,0,1,0,0,1,0]
        Vardy= [0,0,0,0,0,2,0,0]
        Maskdy=0xff
        OutDiff=0x40

        P1 = VerfyProb(InDiffs,Maskdy,OutDiff, n, a, b)


        print(P1)
        print("The number of solutions is",2**8*P1)
        if P1!= 0:
            print(mt.log2(P1))

        Maskdy = 0xbf
        OutDiff = 0x00

        P2 = TESTProb(0b00000010,0xbf,0x00,n=n,a=a,b=b)
        print(P2)
        if P2!= 0:
            print(mt.log2(P2))


        Vardx=[0,0,0,0,0,1,0,1]
        Vardy= [2,0,2,0,0,2,0,0]

        P2,v,d = CalculateProb(Vardx, Vardy, n, a, b)
        print("******************")
        print(P2)
        print("{:08b}".format(v))
        print("{:08b}".format(d))
        if P2!= 0:
            print(mt.log2(P2))





