from pysat.solvers import Solver
from pysat.formula import *
import numpy as np
import  os
import sys
import time
import math as mt
import SIMECK as SM


def HW(X,WordSize):
    Counter=0
    for i in range(WordSize):
        if (X>>i)&1:
            Counter+=1
    return  Counter



class SIMECK():
    def __init__(self,WordSize=16,Alpha=5,Beta=0,Gamma=1):
        self.WordSize=WordSize
        self.n = WordSize * 2


        assert Alpha>Beta,"Error!"
        self.Alpha=Alpha
        self.Beta=Beta
        self.Gamma=Gamma

        #self.varpool = IDPool()
        self.NumHex = str(2 * self.WordSize // 4)
        self.TempStr = "0x{:0" + self.NumHex + "x}"

        #MatSuiBound Linear
        self.SIMECKLinearBound={
            "32":[0,1,2,3,4,6,7,9,10,13,15,17,18,19,20,21,22,24,25,27,28,31,33,35,36,37,38,39,40,42,43,45],
            "48":[0,1,2,3,4,6,7,9,10,13,15,18,19,22,23,25,26,29,31,33,34,36,37,39,40,43,45,48,49,52,53,55,56,59,61,63],
            "64":[0,1,2,3,4,6,7,9,10,13,15,18,19,22,24,27,28,31,
                  32,33,34,36,37,39,40,43,45,48,49,52,54,57,58,61,62,63],
            "96":[0,1,2,3,4,6,7,9,10,13,15,18,19,22,24,27,28,31,
                  32,33,34,36,37,39,40,43,45,48,49,52,54,57,58,61,62,63],
            "128":[0,1,2,3,4,6,7,9,10,13,15,18,19,22,24,27,28,31,
                   32,33,34,36,37,39,40,43,45,48,49,52,54,57,58,61,52,63]



        }

    def ID(self,Name):
        return self.varpool.id(Name)


    def XOR(self,list,SpecialCondition=[]):
        #Do not introduce Auxiliary variables
        for i in range(2**len(list)):
            Counter=HW(i,len(list))
            if Counter&1:   #exclude the current point
                list_Copy=list.copy()

                for j in range(len(list)):
                    if   (i>>j )&1:
                        list_Copy[j]=-list_Copy[j]

                self.SOLVER.add_clause(SpecialCondition+list_Copy)
        return



    def equal(self,list,SpecialCondition=[]):
        for i in range(len(list) - 1):
            self.SOLVER.add_clause([list[i], -list[i + 1]]+SpecialCondition)
            self.SOLVER.add_clause([-list[i], list[i + 1]]+SpecialCondition)
        return

    def OR(self,list, Out):
        self.SOLVER.add_clause(list + [-Out])
        for i in list:
            self.SOLVER.add_clause([-i, Out])
        return

    def NEG(self,list):
        return [-i for i in list]

    def AND(self,list, Out):
        for i in list:
            self.SOLVER.add_clause([i, -Out])
        self.SOLVER.add_clause(self.NEG(list) + [Out])
        return


    def SequentialAddition(self, list, MinSum,MaxSum,MinBoundLimits={}):
        """
           MinSum   <=   Hamming weight (list) <= MaxSum
        :param list:
        :param MinSum:
        :param MaxSum:
        :return:
        """
        #assert MaxSum>=MinSum,""


        AllVars=[]
        if MaxSum==0:
            for i in list:
                self.SOLVER.add_clause([-i])
            return

        NumVars=len(list)
        LastBit=list[-1]
        for ColumnNum  in range(2, NumVars ):#    The number of bits added

            CurrentNumBits=min([ColumnNum,MaxSum])
            if ColumnNum==2:
                OldSum=[list[0]]

            CurrentSum=[ self.varpool.id() for i in range(CurrentNumBits)]
            CurrentBit=list[ColumnNum-1]


            if ColumnNum in MinBoundLimits.keys():
                if MinBoundLimits[ColumnNum]>MaxSum:
                    self.SOLVER.add_clause([CurrentBit])
                    self.SOLVER.add_clause([-CurrentBit])
                    print("Must not be satisfied!")
                else:
                    self.SOLVER.add_clause([CurrentSum[MinBoundLimits[ColumnNum]-1]])


            self.OR([OldSum[0], CurrentBit], CurrentSum[0])


            for row in range(len(OldSum)):
                    self.SOLVER.add_clause([-OldSum[row],CurrentSum[row] ])
                    if (row+1)<len(CurrentSum):
                        self.SOLVER.add_clause([-OldSum[row],-CurrentBit ,CurrentSum[row+1]])
                        self.SOLVER.add_clause([OldSum[row], -CurrentSum[row + 1]])
                    if (row+1)<len(OldSum):
                        self.SOLVER.add_clause([OldSum[row+1],OldSum[row],   -CurrentSum[row + 1]])
                        self.SOLVER.add_clause([OldSum[row + 1], CurrentBit, -CurrentSum[row + 1]])

                    # self.SOLVER.add_clause([OldSum[row],OldSum[row - 1], CurrentBit, -CurrentSum[row]])
                    # self.SOLVER.add_clause([OldSum[row], OldSum[row - 1], -CurrentBit, -CurrentSum[row]])
                    # self.SOLVER.add_clause([OldSum[row], -OldSum[row - 1], CurrentBit, -CurrentSum[row]])

            if ColumnNum>MaxSum:
                self.SOLVER.add_clause([-CurrentBit, -OldSum[-1]])


            OldSum=CurrentSum.copy()
            AllVars.append(OldSum)
            # print(NumVars,ColumnNum)
        # Maximum Bound
        if NumVars>MaxSum:
                self.SOLVER.add_clause([-LastBit, -OldSum[-1]])
        #Minimum Bound
        if MinSum>=1:
            for j in range(MinSum-1):
                self.SOLVER.add_clause([OldSum[j]])
            self.SOLVER.add_clause([ LastBit,  OldSum[MinSum-1]   ])



        return AllVars


    def ConstraintsDiffOneRound(self,A,varbits,doublebits,z,B,Weight,InTD_L,InTD_R,OutTD_L,InR):
        NumBits=len(A)


        for i in range(NumBits):
            i_a= (i+self.Alpha)%self.WordSize
            i_b = (i + self.Beta) % self.WordSize
            i_c = (i + self.Gamma) % self.WordSize
            i_2a_b=(i + 2*self.Alpha-self.Gamma ) % self.WordSize
            i_a_b = (i +  self.Alpha - self.Gamma) % self.WordSize

            #Truncted differential model
            # self.OR([ InTD_L[i_a], InTD_L[i_b],InTD_L[i_c]  ,InTD_R[i]],OutTD_L[i])
            self.SOLVER.add_clause([-InTD_L[i_a], OutTD_L[i] ])
            self.SOLVER.add_clause([-InTD_L[i_b], OutTD_L[i]])
            self.SOLVER.add_clause([-InTD_L[i_c], OutTD_L[i]])
            self.SOLVER.add_clause([-InTD_R[i], OutTD_L[i]])
            # For i-th difference bit,  if the all input difference bit are zero, the ouput difference bit should not be *.
            self.SOLVER.add_clause([InTD_L[i_a], InTD_L[i_b], InTD_L[i_c], InTD_R[i],A[i_a],A[i_b],A[i_c], InR[i], -OutTD_L[i]])

			SpecialCondition=[OutTD_L[i]]
            SpecialCondition2 = [OutTD_L[i],OutTD_L[i_a_b] ]
            

            #Differential model of the round function of  SMION
            self.SOLVER.add_clause(SpecialCondition+[-A[i_a], varbits[i]] )
            self.SOLVER.add_clause(SpecialCondition+[-A[i_b], varbits[i]])
            self.SOLVER.add_clause(SpecialCondition+[A[i_a],A[i_b], -varbits[i]])
            self.SOLVER.add_clause(SpecialCondition2+[A[i_b],- doublebits[i]])
            self.SOLVER.add_clause(SpecialCondition2+[-A[i_b], A[i_2a_b],- doublebits[i]])
            self.SOLVER.add_clause(SpecialCondition2+[-A[i_a], -A[i_b], - doublebits[i]])
            self.SOLVER.add_clause(SpecialCondition2+[A[i_a],-A[i_b], -A[i_2a_b],  doublebits[i]])

            self.SOLVER.add_clause(SpecialCondition+[varbits[i],-z[i]])
            self.SOLVER.add_clause(SpecialCondition+[-doublebits[i],z[i],-z[i_a_b]])
            self.SOLVER.add_clause(SpecialCondition+[-doublebits[i], -z[i],z[i_a_b]])




          
            self.XOR([A[i_c], B[i], z[i]],SpecialCondition=SpecialCondition)
            self.XOR([varbits[i], doublebits[i], Weight[i]],SpecialCondition=SpecialCondition)

            
            self.SOLVER.add_clause([-OutTD_L[i], -z[i]])
            self.SOLVER.add_clause([-OutTD_L[i], -B[i]])
            self.SOLVER.add_clause([-OutTD_L[i], -varbits[i]])
            self.SOLVER.add_clause([-OutTD_L[i], -doublebits[i]])
            self.SOLVER.add_clause([-OutTD_L[i_a_b], -doublebits[i]])  # new added constraint
            self.SOLVER.add_clause([-OutTD_L[i], -Weight[i]])


        return

    def ConstraintsLinearOneRound(self,A,B,G0,G1,LW,):
        NumBits=len(A)

        for i in range(NumBits):
            i_a= (i-self.Alpha)%self.WordSize
            i_b = (i - self.Beta) % self.WordSize
            i_c = (i - self.Gamma) % self.WordSize

            #Linear model
            self.SOLVER.add_clause([B[i], -LW[i] ])
            self.SOLVER.add_clause([-B[i], LW[i]])
            self.SOLVER.add_clause([-G0[i], LW[i]])
            self.SOLVER.add_clause([-G1[i], LW[i]])
            self.XOR([A[i],B[i_c],G0[i_a],G1[i_b]])



        return


    def NameToID(self,L):
        return [self.ID(name) for name in L ]



    def OutputDiffPropagation(self,Model,Round,TrunctedDiff=False):

        print("*******************************")
        print("Diff Part")

        InDiff=0
        OutDiff=0



        #print(Model)
        #Output Differences
        for i in range(len(self.Diff)):
            diff=self.Diff[i]
            for j in range(len(diff)):
                if TrunctedDiff:
                    if self.ID(self.TD_Flag[i][j]) in Model:
                        print(end="*")
                        if i == (len(self.Diff) - 1):
                            OutDiff = OutDiff << 1
                            OutDiff |= 0
                    elif self.ID(diff[j]) in Model:
                        print(end="1")
                        if i == 0:
                            InDiff = InDiff << 1
                            InDiff |= 1
                        if i == (len(self.Diff) - 1):
                            OutDiff = OutDiff << 1
                            OutDiff |= 1

                    elif -self.ID(diff[j]) in Model:
                        print(end="0")
                        if i == 0:
                            InDiff = InDiff << 1
                            InDiff |= 0
                        if i == (len(self.Diff) - 1):
                            OutDiff = OutDiff << 1
                            OutDiff |= 0




                else:

                    if self.ID(diff[j]) in Model:
                        print(end="1")
                        if i==0:
                            InDiff=InDiff<<1
                            InDiff|=1
                        if i == (len(self.Diff)-1):
                            OutDiff = OutDiff << 1
                            OutDiff |= 1

                    elif -self.ID(diff[j]) in Model:
                        print(end="0")
                        if i == 0:
                            InDiff = InDiff << 1
                            InDiff |= 0
                        if i == (len(self.Diff) - 1):
                            OutDiff = OutDiff << 1
                            OutDiff |= 0
            print()



        assert len(self.Weight)>0,""
        CounterWeight=0
        #Output probabilities
        for i in range(len(self.Weight)):
            prob = self.Weight[i]
            for j in range(len(prob)):
                if self.ID(prob[j]) in Model:
                    print(end="1")
                    CounterWeight+=1
                elif -self.ID(prob[j]) in Model:
                    print(end="0")
            print()

        print("Differential Weight:\t", CounterWeight)
        print("Round:\t", Round)
        NumHex=str(2*self.WordSize//4)
        TempStr="{:0"+NumHex+"x}"
        print("In Diff.:\t",TempStr.format(InDiff))
        print("Out Diff.:\t", TempStr.format(OutDiff))
        return InDiff, OutDiff,CounterWeight
    def OutputPropagation(self, Model, Diff_OR_Linear,Weight,TrunctedDiff=False):

        InDiff = 0
        OutDiff = 0
        print("*******************************************")
        # print(Model)
        # Output Differences
        for i in range(len(Diff_OR_Linear)):
            diff = Diff_OR_Linear[i]
            for j in range(len(diff)):
                if TrunctedDiff:
                    if self.ID(self.TD_Flag[i][j]) in Model:
                        print(end="*")
                        if i == (len(Diff_OR_Linear) - 1):
                            OutDiff = OutDiff << 1
                            OutDiff |= 0
                    elif self.ID(diff[j]) in Model:
                        print(end="1")
                        if i == 0:
                            InDiff = InDiff << 1
                            InDiff |= 1
                        if i == (len(Diff_OR_Linear) - 1):
                            OutDiff = OutDiff << 1
                            OutDiff |= 1

                    elif -self.ID(diff[j]) in Model:
                        print(end="0")
                        if i == 0:
                            InDiff = InDiff << 1
                            InDiff |= 0
                        if i == (len(Diff_OR_Linear) - 1):
                            OutDiff = OutDiff << 1
                            OutDiff |= 0




                else:

                    if self.ID(diff[j]) in Model:
                        print(end="1")
                        if i == 0:
                            InDiff = InDiff << 1
                            InDiff |= 1
                        if i == (len(Diff_OR_Linear) - 1):
                            OutDiff = OutDiff << 1
                            OutDiff |= 1

                    elif -self.ID(diff[j]) in Model:
                        print(end="0")
                        if i == 0:
                            InDiff = InDiff << 1
                            InDiff |= 0
                        if i == (len(Diff_OR_Linear) - 1):
                            OutDiff = OutDiff << 1
                            OutDiff |= 0
            print()

        # Output probabilities
        CounterWeight=0
        for i in range(len(Weight)):
            prob = Weight[i]
            for j in range(len(prob)):
                if self.ID(prob[j]) in Model:
                    print(end="1")
                    CounterWeight+=1
                elif -self.ID(prob[j]) in Model:
                    print(end="0")
            print()

        print(" Weight:\t", CounterWeight)
        print("Round:\t", len(Diff_OR_Linear)-1)
        NumHex = str(2 * self.WordSize // 4)
        TempStr = "{:0" + NumHex + "x}"
        print("In :\t", TempStr.format(InDiff))
        print("Out :\t", TempStr.format(OutDiff))
        return InDiff,OutDiff,CounterWeight

    def SearchDiffStepByStep(self,Round,TrunctedDiff=False,NumTrails= 1,StartWeight=0,SpecfiedDiff=[0,0],SolverName="cadical153"):

        CurrentWeight=StartWeight
        NumObtainedTrails=0
        AllTrailsObtained=[]
        AllTrailsObtained2=[]
        while(True):
            print("Searching trails with Hamming weight:",CurrentWeight)
            Flag,Model,TempTrail= self.SearchDiff(Round, CurrentWeight, TruncatedDiff=TrunctedDiff,SpecfiedDiff=SpecfiedDiff, SolverName=SolverName,
                                        AllTrailsObtained=AllTrailsObtained)
            if not Flag:
                CurrentWeight+=1
            else:
                NumObtainedTrails+=1
                AllTrailsObtained.append(Model)

                AllTrailsObtained2.append(TempTrail+[Round])
                #print(AllTrailsObtained)
                if NumObtainedTrails>=NumTrails:
                    break
        return  AllTrailsObtained2








    def SearchDiff(self,Round,TargetWeight,TruncatedDiff=False,SpecfiedDiff=[0,0],SolverName="cadical153",AllTrailsObtained=[]):
        #1.Variables
        self.Diff=[
            ["d{}_R{}".format(i,r) for i in range(self.n)] for r in range(Round+1)
        ]

        self.TD_Flag = [
                ["td{}_R{}".format(i, r) for i in range(self.n)] for r in range(Round + 1)
            ]

        self.Weight = [
            ["w{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round )
        ]

        self.varibits=[
            ["var{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round )
        ]

        self.doublevar = [
            ["doublevar{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round)
        ]

        self.z = [
            ["z{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round)
        ]

        self.B = [
            ["B{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round)
        ]



        self.varpool=IDPool()
        #2. state the variables in the model
        for Name in np.array(self.Diff).flatten():
            self.ID(Name)
        for Name in np.array(self.TD_Flag).flatten():
            self.ID(Name)
        for Name in np.array(self.Weight).flatten():
            self.ID(Name)
        for Name in np.array(self.varibits).flatten():
            self.ID(Name)
        for Name in np.array(self.doublevar).flatten():
            self.ID(Name)
        for Name in np.array(self.z).flatten():
            self.ID(Name)
        for Name in np.array(self.B).flatten():
            self.ID(Name)



        self.SOLVER=Solver(name=SolverName)


        #3. add constrints of differential propagation to the model
        for r in range(Round):
            InL=self.NameToID(self.Diff[r][:self.WordSize])
            InR=self.NameToID(self.Diff[r][self.WordSize:])
            OutL=self.NameToID(self.Diff[r+1][:self.WordSize])
            OutR=self.NameToID(self.Diff[r+1][self.WordSize:])
            TempWeight=self.NameToID(self.Weight[r])

            InTD_L = self.NameToID(self.TD_Flag[r][:self.WordSize])
            InTD_R = self.NameToID(self.TD_Flag[r][self.WordSize:])
            OutTD_L = self.NameToID(self.TD_Flag[r + 1][:self.WordSize])
            OutTD_R = self.NameToID(self.TD_Flag[r + 1][self.WordSize:])

            self.ConstraintsDiffOneRound(InL, self.NameToID(self.varibits[r]), self.NameToID(self.doublevar[r]),
                                         self.NameToID(self.z[r]), self.NameToID(self.B[r]), TempWeight, InTD_L, InTD_R,
                                         OutTD_L,InR)


            for i in range(self.WordSize):
                SpecialCondition = [OutTD_L[i]]
                self.XOR([self.NameToID(self.B[r])[i],InR[i],OutL[i]],SpecialCondition)
                self.SOLVER.add_clause([-OutTD_L[i],- OutL[i]  ])

                self.equal([InL[i],OutR[i]])
                self.equal([InTD_L[i],OutTD_R[i]])


        #Truncated diff model
        for r in range(1 if TruncatedDiff else Round + 1):
            for td in self.NameToID(self.TD_Flag[r]):
                    self.SOLVER.add_clause([- td])
        #the output difference must be not all *.
        if TruncatedDiff:
            self.SOLVER.add_clause(self.NEG(self.NameToID(self.TD_Flag[-1])))



        #jia_le_eq(self.SOLVER, self.varpool, self.NameToID(np.array(self.Weight).flatten()), TargetWeight)
        AllVars=self.SequentialAddition(self.NameToID(np.array(self.Weight).flatten()) ,TargetWeight,TargetWeight)

        #Input Difference is no-zero
        self.SOLVER.add_clause( self.NameToID(self.Diff[0])  )

        #Specify the input difference
        if SpecfiedDiff[0]!=0:
            for i in range(self.WordSize*2):
                if (SpecfiedDiff[0]>>i)&1:
                    self.SOLVER.add_clause([self.NameToID(self.Diff[0])[-1-i]])
                else:
                    self.SOLVER.add_clause([-self.NameToID(self.Diff[0])[-1 - i]])
        # Specify the output difference
        if SpecfiedDiff[1]!=0:
            for i in range(self.WordSize*2):
                if (SpecfiedDiff[1]>>i)&1:
                    self.SOLVER.add_clause([self.NameToID(self.Diff[-1])[-1-i]])
                else:
                    self.SOLVER.add_clause([-self.NameToID(self.Diff[-1])[-1 - i]])


        #Exclude the trails obtained
        for trail in AllTrailsObtained:
            ExcludePoint=self.NEG(trail)
            #print(ExcludePoint)
            self.SOLVER.add_clause(ExcludePoint)


        #4.Solve the model
        Result=self.SOLVER.solve()
        if Result:
            Model=self.SOLVER.get_model()
            # 5.Ouput the result
            InDiff, OutDiff,CounterWeight=self.OutputDiffPropagation(Model, Round, TruncatedDiff)

            # #6.Output the Additions
            # for i in AllVars:
            #     for j in i:
            #         if j in Model:
            #             print(end="1")
            #         elif -j in Model:
            #             print(end="0")
            #         else:
            #             print(end="ERROR")
            #     print()


            return  True,Model,[InDiff, OutDiff,CounterWeight]
        else:
            return False,None,None


    def SearchLinearStepByStep(self,Round,NumTrails= 1,StartWeight=0,SolverName="cadical153"):

        CurrentWeight=StartWeight
        NumObtainedTrails=0
        AllTrailsObtained=[]
        while(True):
            print("Searching trails with Hamming weight:",CurrentWeight)
            Flag,Model= self.SearchLinear( Round, CurrentWeight, AllTrailsObtained=AllTrailsObtained)

            if not Flag:
                CurrentWeight+=1
            else:
                NumObtainedTrails+=1
                AllTrailsObtained.append(Model)
                #print(AllTrailsObtained)
                if NumObtainedTrails>=NumTrails:
                    break






            #if Flag:


    def SearchLinear(self,Round,TargetWeight,SolverName="cadical153",AllTrailsObtained=[]):
        #1.Variables
        self.Linear=[
            ["l{}_R{}".format(i,r) for i in range(self.n)] for r in range(Round+1)
        ]

        self.A = [
            ["A{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round + 1)
        ]

        self.LinearWeight = [
            ["lw{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round )
        ]

        self.Gamma0=[
            ["G0_{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round )
        ]

        self.Gamma1 = [
            ["G1_{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round)
        ]

        self.varpool=IDPool()
        #2. state the variables in the model
        for Name in np.array(self.Linear).flatten():
            self.ID(Name)
            for Name in np.array(self.A).flatten():
                self.ID(Name)
        for Name in np.array(self.LinearWeight).flatten():
            self.ID(Name)
        for Name in np.array(self.Gamma0).flatten():
            self.ID(Name)
        for Name in np.array(self.Gamma1).flatten():
            self.ID(Name)




        self.SOLVER=Solver(name=SolverName)


        #3. add constrints of differential propagation to the model
        for r in range(Round):
            InL=self.NameToID(self.Linear[r][:self.WordSize])
            InR=self.NameToID(self.Linear[r][self.WordSize:])
            OutL=self.NameToID(self.Linear[r+1][:self.WordSize])
            OutR=self.NameToID(self.Linear[r+1][self.WordSize:])
            TempWeight=self.NameToID(self.LinearWeight[r])
            TempA=   self.NameToID(self.A[r])


            self.ConstraintsLinearOneRound(TempA,InR,
                                           self.NameToID(self.Gamma0[r]),self.NameToID(self.Gamma1[r])
                                           ,TempWeight)


            for i in range(self.WordSize):

                self.XOR([InL[i],OutR[i],TempA[i]])
                self.equal([InR[i],OutL[i]])

        # Input Mask is no-zero
        self.SOLVER.add_clause(self.NameToID(self.Linear[0]))


        #jia_le_eq(self.SOLVER, self.varpool, self.NameToID(np.array(self.Weight).flatten()), TargetWeight)
        AllVars=self.SequentialAddition(self.NameToID(np.array(self.LinearWeight).flatten()) ,TargetWeight,TargetWeight)


        #Exclude the trails obtained
        for trail in AllTrailsObtained:
            ExcludePoint=self.NEG(trail)
            #print(ExcludePoint)
            self.SOLVER.add_clause(ExcludePoint)


        #4.Solve the model
        Result=self.SOLVER.solve()
        if Result:
            Model=self.SOLVER.get_model()
            # 5.Ouput the result

            self.OutputPropagation( Model, TargetWeight, self.Linear, self.LinearWeight )



            return  True,Model
        else:
            return False,None


    def SearchDiffLinear(self, Round,RoundLinear, TargetWeight, SolverName="cadical153", AllTrailsObtained=[],
                         HWInDIffL=-1,HWInDIffR=-1,
                         InDiff=[],
                         MatSuiBound=False):



            # 1.Variables
            self.Diff = [
                ["d{}_R{}".format(i, r) for i in range(self.n)] for r in range(Round + 1)
            ]

            self.TD_Flag = [
                ["td{}_R{}".format(i, r) for i in range(self.n)] for r in range(Round + 1)
            ]

            self.Weight = [
                ["w{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round)
            ]

            self.varibits = [
                ["var{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round)
            ]

            self.doublevar = [
                ["doublevar{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round)
            ]

            self.z = [
                ["z{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round)
            ]

            self.B = [
                ["B{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(Round)
            ]

            self.Linear = [
                ["l{}_R{}".format(i, r) for i in range(self.n)] for r in range(RoundLinear + 1)
            ]

            self.A = [
                ["A{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(RoundLinear )
            ]

            self.LinearWeight = [
                ["lw{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(RoundLinear)
            ]

            self.Gamma0 = [
                ["G0_{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(RoundLinear)
            ]

            self.Gamma1 = [
                ["G1_{}_R{}".format(i, r) for i in range(self.WordSize)] for r in range(RoundLinear)
            ]



            self.varpool = IDPool()
            # 2. state the variables in the model
            for Name in np.array(self.Diff).flatten():
                self.ID(Name)
            for Name in np.array(self.TD_Flag).flatten():
                self.ID(Name)
            for Name in np.array(self.Weight).flatten():
                self.ID(Name)
            for Name in np.array(self.varibits).flatten():
                self.ID(Name)
            for Name in np.array(self.doublevar).flatten():
                self.ID(Name)
            for Name in np.array(self.z).flatten():
                self.ID(Name)
            for Name in np.array(self.B).flatten():
                self.ID(Name)

            # 2. state the variables in the model
            for Name in np.array(self.Linear).flatten():
                self.ID(Name)
            for Name in np.array(self.A).flatten():
                self.ID(Name)
            for Name in np.array(self.LinearWeight).flatten():
                self.ID(Name)
            for Name in np.array(self.Gamma0).flatten():
                self.ID(Name)
            for Name in np.array(self.Gamma1).flatten():
                self.ID(Name)


            self.SOLVER = Solver(name=SolverName)

            # ********************************************************
            #
            #                       Truncated Differential Model

            #Using TruncatedDiff  to search differential-linear approximation
            TruncatedDiff=True
            # 3. add constrints of differential propagation to the model
            for r in range(Round):
                InL = self.NameToID(self.Diff[r][:self.WordSize])
                InR = self.NameToID(self.Diff[r][self.WordSize:])
                OutL = self.NameToID(self.Diff[r + 1][:self.WordSize])
                OutR = self.NameToID(self.Diff[r + 1][self.WordSize:])
                TempWeight = self.NameToID(self.Weight[r])

                InTD_L = self.NameToID(self.TD_Flag[r][:self.WordSize])
                InTD_R = self.NameToID(self.TD_Flag[r][self.WordSize:])
                OutTD_L = self.NameToID(self.TD_Flag[r + 1][:self.WordSize])
                OutTD_R = self.NameToID(self.TD_Flag[r + 1][self.WordSize:])

                self.ConstraintsDiffOneRound(InL, self.NameToID(self.varibits[r]), self.NameToID(self.doublevar[r]),
                                             self.NameToID(self.z[r]), self.NameToID(self.B[r]), TempWeight, InTD_L,
                                             InTD_R,
                                             OutTD_L,InR)

                for i in range(self.WordSize):
                    SpecialCondition = [OutTD_L[i]]
                    self.XOR([self.NameToID(self.B[r])[i], InR[i], OutL[i]], SpecialCondition)
                    self.SOLVER.add_clause([-OutTD_L[i], - OutL[i]])

                    self.equal([InL[i], OutR[i]])
                    self.equal([InTD_L[i], OutTD_R[i]])

            # Truncated diff model
            for r in range(1 if TruncatedDiff else Round + 1):
                for td in self.NameToID(self.TD_Flag[r]):
                    self.SOLVER.add_clause([- td])
            # the output difference must be not all *.
            if TruncatedDiff:
                self.SOLVER.add_clause(self.NEG(self.NameToID(self.TD_Flag[-1])))

            # Input Difference is no-zero
            self.SOLVER.add_clause(self.NameToID(self.Diff[0]))
            #********************************************************
            #
            #                       Linear Model

            # 3. add constrints of Linear propagation to the model
            for r in range(RoundLinear):
                InL = self.NameToID(self.Linear[r][:self.WordSize])
                InR = self.NameToID(self.Linear[r][self.WordSize:])
                OutL = self.NameToID(self.Linear[r + 1][:self.WordSize])
                OutR = self.NameToID(self.Linear[r + 1][self.WordSize:])
                TempWeight = self.NameToID(self.LinearWeight[r])
                TempA = self.NameToID(self.A[r])

                self.ConstraintsLinearOneRound(TempA, InR,
                                                     self.NameToID(self.Gamma0[r]), self.NameToID(self.Gamma1[r])
                                                     , TempWeight)

                for i in range(self.WordSize):
                    self.XOR([InL[i], OutR[i], TempA[i]])
                    self.equal([InR[i], OutL[i]])

            # Input Mask is no-zero
            self.SOLVER.add_clause(self.NameToID(self.Linear[0]))

            # ********************************************************
            #
            #                       Conect Point Model

            for i in range(self.n):
                self.SOLVER.add_clause([-self.NameToID(self.TD_Flag[Round])[i] ,-self.NameToID(self.Linear[0])[i]])



            # jia_le_eq(self.SOLVER, self.varpool, self.NameToID(np.array(self.Weight).flatten()), TargetWeight)
            LinearWeightName=np.array(self.LinearWeight).flatten()
            LinearWeightName=np.repeat(LinearWeightName,2)
            LinearWeight=self.NameToID(LinearWeightName)
            DiffWeight=self.NameToID(np.array(self.Weight).flatten())
            AllWeights=LinearWeight+DiffWeight

            # Limit the linear weight
            MinBoundLimits={}
            if MatSuiBound:
                LinearBound = self.SIMECKLinearBound[str(self.WordSize * 2)]
                if LinearBound != []:
                    for r in range(RoundLinear):
                        if LinearBound[r]!=0:
                            MinBoundLimits[(r+1)*self.WordSize*2]=LinearBound[r]*2
                print(MinBoundLimits)


            AllVars = self.SequentialAddition(AllWeights, TargetWeight, TargetWeight,MinBoundLimits=MinBoundLimits)

            # Exclude the trails obtained
            for trail in AllTrailsObtained:
                ExcludePoint = self.NEG(trail)
                #print(ExcludePoint)
                self.SOLVER.add_clause(ExcludePoint)
            #Limit the Hamming weight of input differences


            if HWInDIffL>0:
                InDiffL = self.NameToID(self.Diff[0])[:self.WordSize]
                AllVars = self.SequentialAddition(InDiffL, HWInDIffL, HWInDIffL)

            if HWInDIffR > 0:
                InDiffR = self.NameToID(self.Diff[0])[self.WordSize:]
                AllVars = self.SequentialAddition(InDiffR, HWInDIffR, HWInDIffR)

            if InDiff!=[]:
                InDiffL = self.NameToID(self.Diff[0])[:self.WordSize]
                InDiffR = self.NameToID(self.Diff[0])[self.WordSize:]
                for i in range(self.WordSize):
                    if (InDiff[0]>>(self.WordSize-1-i))&1:
                        self.SOLVER.add_clause([InDiffL[i]])
                    else:
                        self.SOLVER.add_clause([-InDiffL[i]])

                    if (InDiff[1] >> (self.WordSize - 1 - i)) & 1:
                        self.SOLVER.add_clause([InDiffR[i]])
                    else:
                        self.SOLVER.add_clause([-InDiffR[i]])

            # #Limit the linear weight
            # if MatSuiBound:
            #     LinearBound=self.SIMECKLinearBound[str(self.WordSize*2)]
            #
            #     if LinearBound!=[]:
            #
            #         for r in range(RoundLinear):
            #             LinearWeightName=[]
            #             for i in range(r+1):
            #                 LinearWeightName+=self.LinearWeight[i]
            #
            #             LinearWeight = self.NameToID(LinearWeightName)
            #             MinWeight=LinearBound[r]
            #             AllVars = self.SequentialAddition(LinearWeight, MinWeight, self.WordSize)#The MaxSum is enough big number（self.WordSize）
            #     else:
            #         assert False,"Set Matsui bound error!"
            # 4.Solve the model
            Result = self.SOLVER.solve()
            if Result:
                Model = self.SOLVER.get_model()
                # 5.Ouput the result
                #Diff part
                InDiff,OutDiff,DiffProb=self.OutputDiffPropagation(Model, Round, TruncatedDiff)
                #Linear part
                InMask,OutMask,LinearProb=self.OutputPropagation(Model, self.Linear, self.LinearWeight)

                NumHex = str(2 * self.WordSize // 4)
                TempStr = "{:0" + NumHex + "x}"
                #determine the input difference and output Mask
                print("Total Round:\t",Round+RoundLinear)
                print("Diff part:\t",Round,"\tLinear part:\t",RoundLinear)
                print("Weight:\t",TargetWeight)
                print("In Diff:\t",TempStr.format(InDiff))
                print("Out Mask:\t", TempStr.format(OutMask))
                #print(self.varpool.id2obj)
                return True, Model,[InDiff,InMask,OutMask,TargetWeight,Round,RoundLinear,DiffProb,LinearProb]
            else:
                return False, None,[]
    def SearchDiffLinearStepByStep(self,Round,RoundLinear,NumTrails= 1,StartWeight=0,SolverName="cadical153",
                                   HWInDIffL=-1,HWInDIffR=-1,
                                   InDiff=[],
                                   MatSuiBound=False):

        CurrentWeight=StartWeight
        NumObtainedTrails=0
        AllTrailsObtained=[]
        AllResult=[]
        while(True):
            print("Searching trails with Hamming weight:",CurrentWeight)
            Flag,Model,DL_Info= self.SearchDiffLinear(Round, RoundLinear,CurrentWeight, SolverName=SolverName,
                                        AllTrailsObtained=AllTrailsObtained,HWInDIffL=HWInDIffL,HWInDIffR=HWInDIffR,
                                                      InDiff=InDiff,
                                                      MatSuiBound=MatSuiBound)
            if not Flag:
                CurrentWeight+=1
            else:
                AllResult.append(DL_Info)
                NumObtainedTrails+=1
                AllTrailsObtained.append(Model)
                #print(AllTrailsObtained)
                if NumObtainedTrails>=NumTrails:
                    break
            print()
        print(AllTrailsObtained)
        return AllResult





            #if Flag:

    def SearchDiffLinearTop(self, Round, RoundLinear,ScopeRound=2 ,NumTrails=1, StartWeight=0, SolverName="cadical153",
                            HWInDIffL=-1,HWInDIffR=-1,InDiff=[],MatSuiBound=False):
        AllResult=[]
        AllTest=[]
        TotalRound=Round+RoundLinear

        #determine the search range
        for i in range(-ScopeRound,ScopeRound+1 ):
            TempRound=Round+i
            TempRoundLinear=RoundLinear-i
            if (TempRound<=TotalRound)&(0<=TempRound)&(TempRoundLinear<=TotalRound)&(TempRoundLinear>=0):
                AllTest.append([TempRound,TempRoundLinear])
        print("The range of search:")
        print(AllTest)
        for tempConf in AllTest:

            TempResult=self.SearchDiffLinearStepByStep(tempConf[0],tempConf[1],NumTrails= NumTrails,StartWeight=StartWeight,
                                            SolverName=SolverName,HWInDIffL=HWInDIffL,HWInDIffR=HWInDIffR,
                                                       InDiff=InDiff,
                                                       MatSuiBound=MatSuiBound)
            AllResult+=TempResult
        SortedRes=sorted(AllResult,key=lambda i:i[2])
        StrRes=[ [  self.TempStr.format(temp[i]) if i <3 else temp[i]  for i in range(len(temp))] for temp in SortedRes]
        print("The final result of search:")
        print(StrRes)








class Logger(object):
    def __init__(self, file_name="Default.log", stream=sys.stdout):
        self.terminal = stream
        self.log = open(file_name, "a")
    def write(self, message):
        self.terminal.write(message)
        self.log.write(message)
    def flush(self):
        pass

if __name__ == "__main__":

    SearchDiff=True
    SearchLinear=False
    SearchDl=False


    if SearchDiff:
        WordSize = 32


        Round = 5

        NumTrails = 3
        TrunctedDiff = False
        SpecfiedDiff=[0,0x0a000000_10000000]

        # ******************************************************
        #
        #                   Search process
        SampleSIMECK = SIMECK(WordSize=WordSize)
        SampleSIMECK.SearchDiffStepByStep(Round,TrunctedDiff=TrunctedDiff,NumTrails= NumTrails,StartWeight=0,SpecfiedDiff=SpecfiedDiff,SolverName="cadical153")

    if SearchLinear:
        WordSize = 16


        Round = 8

        NumTrails = 3

        # ******************************************************
        #
        #                   Search process
        SampleSIMECK = SIMECK(WordSize=WordSize)
        SampleSIMECK.SearchLinearStepByStep(Round,NumTrails)

    if  SearchDl:

        WordSize=32
        SearchConf={"32":[9,5,15],
                    "48":[11,6,20],
                    "64":[15,5,15],

                    }

        HWInDIffL = -1
        HWInDIffR = -1

        # Limit the input difference
        InDiff = [1, 0]

        Round=SearchConf[str(WordSize*2)][0]
        RoundLinear=SearchConf[str(WordSize*2)][1]
        StartWeight =SearchConf[str(WordSize*2)][2]


        NumTrails=8
        TrunctedDiff=True




        #******************************************************
        #
        #                   Log configuration

        log_path = './Logs/'
        if not os.path.exists(log_path):
            os.makedirs(log_path)
        NAME="SIMECK"+str(WordSize*2)+"_Conf_"+str(Round+RoundLinear)+"(" +str(Round)+","+ str(RoundLinear)+")-"

        if (HWInDIffL>0) |(HWInDIffR>0):
            NAME+="HWInDiff-（"+str(HWInDIffL)+","+str(HWInDIffR)+")"

        if (InDiff!=[]):
            NAME+="_InDiff_"+str(hex(InDiff[0]))+"_"+str(hex(InDiff[1]))


        log_file_name = log_path + 'log-DLSearch-'+NAME + time.strftime("%Y%m%d-%H%M%S", time.localtime()) + '.log'

        sys.stdout = Logger(log_file_name)

        sys.stderr = Logger(log_file_name)
        #******************************************************

        # ******************************************************
        #
        #                   Search process
        SampleSIMECK=SIMECK(WordSize=WordSize)
        #SampleSIMECK.SearchDiffStepByStep(Round,TrunctedDiff=False,NumTrails= NumTrails,StartWeight=0,SolverName="cadical153")
        #SampleSIMECK.SearchLinearStepByStep(Round,NumTrails)

        #SampleSIMECK.SearchDiffLinearStepByStep( Round, RoundLinear, NumTrails=NumTrails,)
        SampleSIMECK.SearchDiffLinearTop( Round, RoundLinear,ScopeRound=2 ,NumTrails=NumTrails,StartWeight=StartWeight,
                                         HWInDIffL=HWInDIffL,HWInDIffR=HWInDIffR,
                                          InDiff=InDiff
                                         )



   





