%Declarações inicias.
%:- use_module(library(lists)).

:- op(900, xfy, '::').

:- dynamic cliente/2.
:- dynamic meioTransporte/5.
:- dynamic estafeta/2.
:- dynamic morada/3.
:- dynamic entrega/7.
:- dynamic encomenda/3.
:- dynamic taxapraxo/3.
:- dynamic precoServico/5.
:- dynamic data/4.


% I don't know what this does but SWI Prolog told me to put it here so I will
:- discontiguous (+)/1.


%Construção_dabase_de conhecimento%
+data(H,D,M,A) :: (data(H,D,M,A),
   H>=1,
   H=<24,
   A>=2020,
   D>=1
   , (
(member(M, [1,3,5,7,8,10,12]), D=<31);
(member(M, [2]), D=<28);
(member(M, [2]), 0 is mod(A,4), D=<29);
(member(M, [4,6,9,11]), D=<30)
)).


%invariantes estruturais de inserção que permitemque seja adicionado à base de conhecimento 
%um cliente/estafeta

+cliente(Id,L) :- length(L,V),
  V is 0,
  findall(Id,cliente(Id,_),Lista), length(Lista,N), 
  N==1,
  Id>0.

+meioTransporte(_,Preco,Vel,Taxa,ClassEco) :-
	Preco > 0,
	Vel > 0,
	Taxa > 0,
	ClassEco > 0.


% IdEntrega,IdCliente,IdEstafeta,IdMorada,Horai,Diai,Mesi,Anoi,Horaf,DiaF,MesF,AnoF,Avaliação
+entrega(IdEntrega,IdCliente,IdEstafeta, IdMorada,data(Hi,Di,Mi,Ai),data(Hf,Df,Mf,Af),Aval) :-
	findall(IdEntrega, entrega(IdEntrega,_,_,_,_,_,_), Lst), length(Lst, Len), Len == 1,
	cliente(IdCliente,_),
	estafeta(IdEstafeta,_),
	morada(IdMorada,_,_),
	Hi >= 1,
	Hi =< 24,
	Hf >= 1,
	Hf =< 24,
	dataMaior(data(Hi,Di,Mi,Ai), data(Hf,Df,Mf,Af)),
	(
	(member(Mi, [1,3,5,7,8,10,12]), Di=<31);
	(member(Mi, [2]), Di=<28);
	(member(Mi, [2]), 0 is mod(Ai,4), Di=<29);
	(member(Mi, [4,6,9,11]), Di=<30)
	),(
	(member(Mf, [1,3,5,7,8,10,12]), Df=<31);
	(member(Mf, [2]), Df=<28);
	(member(Mf, [2]), 0 is mod(Af,4), Df=<29);
	(member(Mf, [4,6,9,11]), Df=<30)
	),
	Aval >= 0,
	Aval =< 5.

+estafeta(IdEstafeta, LE) :-
	findall(IdEstafeta, estafeta(IdEstafeta,_), Lst), length(Lst, Len), Len == 1,
	length(LE, LenLE), LenLE == 0.

+morada(IdMorada, _,_) :-
	findall(IdMorada, morada(IdMorada,_,_), Lst), length(Lst, Len), Len == 1.

+encomenda(IdEntrega, Peso, Volume) :-
	entrega(IdEntrega,_,_,_,_,_,_),
	Peso > 0,
	Volume > 0.

+taxaPrazo(Duracao, Preco) :-
	Duracao >= 0,
	Preco > 0.

max_aux([(D,T)],(D,T)) :- !, true.
max_aux([(D,_)|Xs], (Dm,Tm)):- max_aux(Xs, (Dm,Tm)), Dm >= D.
max_aux([(D,T)|Xs], (Dm,_)):- max_aux(Xs, (D,T)), D > Dm.

calcTaxaDuracao(Duracao, TaxaD) :-
	findall((D,TaxasD), (taxaPrazo(D,TaxasD), D =< Duracao), Lst),
	max_aux(Lst, (_, TaxaD)).


+precoServico(IdEntrega,Duracao,MeioTransporte,PrecoProduto,PrecoTotal) :-
	entrega(IdEntrega,_,_,_,_,_,_),
	Duracao >= 0,
	calcTaxaDuracao(Duracao, TaxaD),
	meioTransporte(MeioTransporte,_,_,TaxaMT,_),
	PrecoProduto > 0,
	PrecoTotal is TaxaMT + PrecoProduto + TaxaD.

%cliente(#idCliente,[IdEntrega])-> {V,F}.
%cliente/2
cliente(1,[2,4]).
cliente(2,[5]).
cliente(3,[1,9]).
cliente(4,[3,6]).
cliente(5,[7,8,10]).
cliente(6,[12,14]).
cliente(7,[11,16]).
cliente(8,[13]).
cliente(9,[18]).
cliente(10,[17,19]).
cliente(11,[15,20]).

%Extensão do Predicado meioTransporte: Veiculo, PesoMaximo, VelocidadeMedia, Taxa, ClassificaçaoEcologica-> {V,F}.
%meioTransporte/5
meioTransporte(bicicleta, 5, 10, 5, 2).
meioTransporte(mota, 20, 35 , 10, 1).
meioTransporte(carro, 100, 25, 15, 0).


%Extensão do Predicado Estafeta: Id,[IdEntregas]->{V,F}
%estafeta/2
estafeta(1,[2,3,6,7,15]).
estafeta(2,[4,8,13,18]).
estafeta(3,[1,10,14]).
estafeta(4,[5,12,16,19]).
estafeta(5,[9,11,17,20]).



%Extensão do Predicado Morada: Id, Rua, Freguesia->{V,F}.
%morada/3
morada(1,ruaDosPeoes, sao_vitor).
morada(2,ruaOceanoPacifico,valongo).
morada(3,ruaPedroCabral,valongo).
morada(4,ruaDoPapel,amares).
morada(5,ruaJorgeMilk,leitelho).
morada(6,ruaNovaCruz, sao_vitor).
morada(7,ruaNovaCruz, sao_vitor).
morada(8,ruaSaoJoao,manhente).
morada(9,ruaPiao,valongo).
morada(10,ruaPadreGiesteira,marinhas).



%ver idCliente, ou cliente com lista de entregas
%Extensão do Predicado Entrega: Id, IdCliente, IdEstafeta,IdMorada, 
%DataInicial(Horai,Diai,Mesi,Anoi), dataFinal(Horaf, Diaf, Mesf,Anof), Classificação-> {V,F}.
%entrega/7
%Entregues:
entrega(1,3,3,3,data(12,13,12,2021),data(16,13,12,2021),4).
entrega(2,1,1,1,data(20,8,11,2021),data(9,13,12,2021),3).
entrega(3,4,1,4,data(10,11,12,2021),data(13,11,12,2021),5).
entrega(4,1,2,4,data(17,27,11,2021),data(20,27,11,2021),2).
entrega(5,2,4,2,data(12,20,9,2021),data(15,20,9,2021),2).
entrega(6,4,1,10,data(9,13,12,2021),data(13,13,12,2021),5).
entrega(7,5,1,5,data(12,17,10,2021),data(20,17,10,2021),3).
entrega(8,5,2,4,data(16,27,11,2021),data(21,27,11,2021),3).
entrega(9,3,5,3,data(9,31,10,2021),data(16,31,10,2021),4).
entrega(10,5,3,5,data(9,17,10,2021),data(11,17,10,2021),4).
entrega(11,7,5,7,data(9,18,11,2021),data(16,18,11,2021),3).
entrega(12,6,4,6,data(14,1,10,2021),data(19,1,10,2021),4).
entrega(13,8,2,4,data(15,16,10,2021),data(19,16,10,2021),4).
entrega(14,6,3,6,data(13,26,9,2021),data(16,26,9,2021),3).
entrega(15,11,1,1,data(9,3,9,2021),data(12,3,9,2021),3).
entrega(16,7,4,4,data(8,1,10,2021),data(10,1,10,2021),2).
entrega(17,10,5,1,data(14,14,10,2021),data(18,14,10,2021),4).
entrega(18,9,2,9,data(16,8,11,2021),data(18,8,11,2021),4).
entrega(19,10,4,4,data(13,24,10,2021),data(17,24,10,2021),4).
entrega(20,1,1,4,data(9,25,11,2021),data(13,27,11,2021),3).
%Não entregues:
entrega(15,11,1,1,data(9,3,9,2021),data(8,3,9,2021),3).
entrega(16,7,4,4,data(8,1,10,2021),data(7,1,10,2021),2).
entrega(17,10,5,1,data(14,14,10,2021),data(13,14,10,2021),4).
entrega(18,9,2,9,data(16,8,11,2021),data(15,8,11,2021),4).
entrega(19,10,4,4,data(13,24,10,2021),data(12,24,10,2021),4).
entrega(20,1,1,4,data(9,25,11,2021),data(8,25,11,2021),3).

%Extensão do  Predicado Encomenda: IdEntrega, Peso, Volume->{V,F}
%encomenda/4
encomenda(1,20,40).
encomenda(2,5,10).
encomenda(3,18,36).
encomenda(4,100,200).
encomenda(5,34,68).
encomenda(6,71,142).
encomenda(7,2,4).
encomenda(8,77,154).
encomenda(9,3,6).
encomenda(10,15,30).
encomenda(11,11,22).

encomenda(12,20,40).
encomenda(13,5,10).
encomenda(14,22,44).
encomenda(15,24,48).
encomenda(16,19,38).
encomenda(17,1,2).
encomenda(18,4,8).
encomenda(19,75,150).
encomenda(20,7,14).



%Extensão do Predicado TaxaPrazo: Duração, Preco->{V,F}
taxaPrazo(0, 9). 
taxaPrazo(2, 5).
taxaPrazo(4, 3).
taxaPrazo(8, 2).
taxaPrazo(16, 1.5).
taxaPrazo(24, 0.8).


%Extensão do Predicado PreçoServiço:IdEntrega, Duração PMeioTransporte, PreçoProduto, PreçoTotal->{V,F}%

precoServico(1,4,mota,24,37).
precoServico(2,1,bicicleta,71,85).                %precoServico bicicleta-5 mota-10 carro-15, 
precoServico(3,2.5,mota,110,115).
precoServico(4,3,carro,51,71).                    %precoServico
precoServico(5,0.5,carro,72,96).
precoServico(6,5,carro,2,19).
precoServico(7,5,bicicleta,15,23).
precoServico(8,6,carro,15,33).
precoServico(9,7,bicicleta,22,30).
precoServico(10,1,mota,36,55).
precoServico(11,2,mota,34,49).
precoServico(12,4,mota,154,167).
precoServico(13,1,bicicleta,1000,1014).
precoServico(14,25,carro,300,315.8).
precoServico(15,14,carro,89,106).
precoServico(16,13,mota,10,22).
precoServico(17,1,bicicleta,11,25).
precoServico(18,1,bicicleta,200,214).
precoServico(19,3,carro,150,170).
precoServico(20,2,mota,154,169).

%_______________________________
%Queries.

%Extensão do Predicado Entrega: Id, IdCliente, IdEstafeta,IdMorada, Horai, Diai, Mesi, Anoi, Horaf, Diaf, Mesf,Anof, Classificação-> {V,F}.
%entrega/13

% Query 1. Identificar o estafeta que utilizou mais vezes um meio de transporte mais ecológico;
calculaAvaliacao([],0).
calculaAvaliacao([Veiculo|Tail],X):-meioTransporte(Veiculo,_,_,_,ClassificacaoEcologica), %Serve para identificar a ClassificacaoEcologica referente a um veiculo.
												calculaAvaliacao(Tail,NewX), %Rinse and repeat.
												X is NewX+ClassificacaoEcologica. %atualiza o valor de NewX.

lista_IdEntregaToVeiculo([],ListaVeiculo,ListaFinal):- reverse(ListaVeiculo,ListaFinal). %Inverte a lista final.
lista_IdEntregaToVeiculo([IdEntrega|Tail],ListaVeiculo,ListaFinal):- precoServico(IdEntrega,_,Veiculo,_,_), %Serve para identificar o veiculo utilizado na respectiva entrega.
																			 lista_IdEntregaToVeiculo(Tail,[Veiculo|ListaVeiculo],ListaFinal). %Rinse and repeat para o proximo idEntrega.

mostEcologicCourier1([],ListaAvaliacaoEco,ListaFinal):- reverse(ListaAvaliacaoEco,ListaFinal).
mostEcologicCourier1([IdEstafeta|Tail],ListaAvaliacaoEco,ListaFinal):- findall(IdEntrega,entrega(IdEntrega,_,IdEstafeta,_,_,_,_), ListaIdEntrega), %Cria a lista de IdEntrega das entregas que um determinado estafeta realizou.
																			  lista_IdEntregaToVeiculo(ListaIdEntrega,ListaVeiculo,ListaVeiculosFinal), %muda a lista de IdEntrega para lista de Veiculos
																			  calculaAvaliacao(ListaVeiculosFinal,X), %calcula o valor da avaliação ecologica,
																			  length(ListaVeiculosFinal,Y), %calcula o tamanho da lista.
																			  NewX is X/Y, %atualiza o valor do X
																			  mostEcologicCourier1(Tail,[NewX|ListaAvaliacaoEco],ListaFinal). %procede para o proximo Estafeta.


mostEcologicCourier(Result):- findall(IdEstafeta, estafeta(IdEstafeta,_), ListaIdEstafeta), %cria uma lista com os Ids dos estafetas.
									 mostEcologicCourier1(ListaIdEstafeta, ListaAvaliacaoEco,ListaAvaliacaoEcoFinal), %Cria uma lista de avaliações ecologicas dos estafetas.
									 max_list(ListaAvaliacaoEcoFinal, MaxValue), %Procura o maior valor das avaliações ecologicas dos estafetas.
									 nth0(Indice,ListaAvaliacaoEcoFinal, MaxValue), %Calcula o Indice do estafeta que tem o maior valor de avaliação ecologica.
									 Result is Indice+1. %devolve o resultado.

% Query 2. Identificar que estafetas entregaram determinada(s) encomenda(s) a um determinado cliente;

removeRepetidos([],ListaTemp,Result):-reverse(ListaTemp,Result).
removeRepetidos([Id|Tail],ListaTemp,Result):- member(Id,ListaTemp),
																		removeRepetidos(Tail,ListaTemp,Result).
removeRepetidos([Id|Tail],ListaTemp,Result):- \+member(Id,ListaTemp),
																		removeRepetidos(Tail,[Id|ListaTemp],Result).


listClientCouriers(IdCliente,Result):- findall(IdEstafeta, entrega(_,IdCliente,IdEstafeta,_,_,_,_), ListaIdEstafeta),
												removeRepetidos(ListaIdEstafeta,[],Result).


% Query 3. 

listCourierClients(IdEstafeta,Result):- findall(IdCliente, entrega(_,IdCliente,IdEstafeta,_,_,_,_), ListaIdCliente),
												removeRepetidos(ListaIdCliente,[],Result).
% Query 4. F
somaPrecos([],0).
somaPrecos([IdEntrega|Tail],Result):- precoServico(IdEntrega,_,_,_,PrecoF),
												 somaPrecos(Tail,NewResult),
												 Result is NewResult+PrecoF.

profitDay(D,M,A,Result):- findall(IdEntrega,(entrega(IdEntrega,_,_,_,_,data(_,D,M,A),_)), ListaIdEntrega),
						  somaPrecos(ListaIdEntrega,Result).


% Query 5. Identificar quais as zonas (e.g., rua ou freguesia) com maior volume de entregas por parte da Green Distribution;
occ(X,N,L) :-
    occ(L,max(null,0),[],max(X,N)).
occ([], max(Xm, Nm), _, max(Xm, Nm)).
occ([X|L], max(Xm, Nm), Counts, FinalMax) :-

    (   select(X-N, Counts, CountsT)
    ->
        N1 is N+1
    ;
        N1 = 1,
        CountsT = Counts),
    Counts2 = [X-N1 | CountsT],
    (   N1 > Nm
    ->  
        occ(L, max(X,N1), Counts2, FinalMax)
    ;
        occ(L, max(Xm,Nm), Counts2, FinalMax)).

createListaMorada([],Temp,Result):-reverse(Temp, Result).
createListaMorada([X|Tail],Temp,Result):- morada(X, Rua,_),
														createListaMorada(Tail, [Rua|Temp], Result).


mostFrequentZone(Result):- findall(IdMorada, entrega(_,_,_,IdMorada,_,_,_), ListaIdMorada),
								  createListaMorada(ListaIdMorada, Temp, ListaMorada),
								  occ(Result,_,ListaMorada).

								  

% Query 6.
avalAverage(IdEstafeta,Result):- findall(Avaliacao,entrega(_,_,IdEstafeta,_,_,_,Avaliacao),ListaAvaliacao),
                                sumlist(ListaAvaliacao,X),
                                length(ListaAvaliacao,Y),
                                Result is X/Y.
% Query 7.
dataMaior(data(HoraG,DiaG,MesG,AnoG),data(HoraP,DiaP,MesP,AnoP)):-
	(AnoG>AnoP);
	(AnoG==AnoP),(MesG>MesP);
	(AnoG==AnoP),(MesG==MesP),(DiaG>DiaP);
	(AnoG==AnoP),(MesG==MesP),(DiaG==DiaP),(HoraG>HoraP);
	(AnoG==AnoP),(MesG==MesP),(DiaG==DiaP),(HoraG==HoraP).


dataCompreendida(DataInicial,DataFinal,DataTeste):-
	dataMaior(DataTeste,DataInicial),dataMaior(DataFinal,DataTeste).

listfromIdEntregaToVeiculo([],Temp,Result):-
	reverse(Temp,Result).
listfromIdEntregaToVeiculo([X|T],Temp,Result):- 
	precoServico(X,_,Veiculo,_,_),
	listfromIdEntregaToVeiculo(T,[Veiculo|Temp],Result).

devolveOccorencia(_,[],0).
devolveOccorencia(X,[X|T],R):-
	devolveOccorencia(X,T,NewR),
	R is NewR+1. 
devolveOccorencia(X,[H|T],R):-
	devolveOccorencia(X,T,R).

transportUsageInPeriod(DataInicial,DataFinal,Result):- 
	findall(IdEntrega, (entrega(IdEntrega,_,_,_,_,DataTeste,_),dataCompreendida(DataInicial,DataFinal,DataTeste)),ListaIdEntrega),
	listfromIdEntregaToVeiculo(ListaIdEntrega,[],ListaVeiculo),
	devolveOccorencia(bicicleta,ListaVeiculo,OcorrenciaBicicleta),
	devolveOccorencia(mota,ListaVeiculo,OcorrenciaMota),
	devolveOccorencia(carro,ListaVeiculo,OcorrenciaCarro),
	append([[(bicicleta,OcorrenciaBicicleta)],[(mota,OcorrenciaMota)],[(carro,OcorrenciaCarro)]],Result).

% Query 8.

numberDeliveriesInPeriod(DataInicial,DataFinal,Result):-
	findall(IdEntrega, (entrega(IdEntrega,_,_,_,_,DataTeste,_),dataCompreendida(DataInicial,DataFinal,DataTeste)),ListaIdEntrega),
	length(ListaIdEntrega,Result).

% Query 9.

deliveredNotDelivered(Result):-
	findall(IdEntrega, (entrega(IdEntrega,_,_,_,DataInicial,DataFinal,_),dataMaior(DataFinal,DataInicial)),ListaIdEntrega),
	findall(IdEntrega, (entrega(IdEntrega,_,_,_,DataInicial,DataFinal,_),dataMaior(DataInicial,DataFinal)),ListaIdNaoEntrega),
	length(ListaIdEntrega,Entregues),
	length(ListaIdNaoEntrega,NEntregues),
	append([[("Entregues",Entregues)],[("Nao entregues",NEntregues)]],Result).


% Query 10.
totalWeight([],0).
totalWeight([IdEncomenda|T],R):-
	encomenda(IdEncomenda,Peso,_),
	totalWeight(T,NewPeso),
	R is NewPeso+Peso.									

weightCarriedInADay(D,M,A,IdEstafeta,Result):-
	findall(IdEntrega, (entrega(IdEntrega,_,_,_,DataInicial,DataFinal,_), dataMaior(DataFinal,DataInicial),dataCompreendida(data(0,D,M,A),data(23,D,M,A),DataFinal)), ListaIdEntrega),
	totalWeight(ListaIdEntrega,Result).





