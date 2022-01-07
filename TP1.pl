%Declarações inicias.
%:- use_module(library(lists)).

:- op(900, xfy, '::').

:- dynamic cliente/2.
:- dynamic meioTransporte/5.
:- dynamic estafeta/2.
:- dynamic morada/5.
:- dynamic entrega/7.
:- dynamic encomenda/3.
:- dynamic taxapraxo/3.
:- dynamic precoServico/5.
:- dynamic data/4.
:- dynamic ilProfjam2/4.
:- dynamic tail/2.
%:- dynamic distanciaPontos/5


% I don't know what this does but SWI Prolog told me to put it here so I will
:- discontiguous (+)/1.

 pack_install(date_time).


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
	morada(IdMorada,_,_,_,_),
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

+morada(IdMorada, _,_,_,_) :-
	findall(IdMorada, morada(IdMorada,_,_,_,_), Lst), length(Lst, Len), Len == 1.
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



%Extensão do Predicado Morada: Id, Rua, Freguesia,Longitude(x), Latitude(y)->{V,F}.
%morada/5
morada(0,armazem,armazem, 41.205273, -8.530271).
morada(1,ruaJorgeMilk,leitelho,41.209450, -8.568272).
morada(2,ruaPiao,valongo,41.187970, -8.488052).
morada(3,ruaOceanoPacifico,valongo,41.196673, -8.516681).
morada(4,ruaPedroCabral,valongo, 41.178034, -8.459965).
morada(5,ruaDoPapel,amares,41.624043, -8.347159).
morada(6,ruaDosPeoes, sao_vitor,41.557081, -8.398892).
morada(7,ruaNovaCruz, sao_vitor,41.555884, -8.401906).
morada(8,pracaDoBocage, sao_vitor,41.555884, -8.401906).
morada(9,ruaSaoJoao,manhente,41.547938, -8.621399).
morada(10,ruaPadreGiesteira,marinhas,41.544324, -8.784028).





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
entrega(7,5,1,1,data(12,17,10,2021),data(20,17,10,2021),3).
entrega(8,5,2,4,data(16,27,11,2021),data(21,27,11,2021),3).
entrega(9,3,5,3,data(9,31,10,2021),data(16,31,10,2021),4).
entrega(10,5,3,5,data(9,17,10,2021),data(11,17,10,2021),4).
entrega(11,7,5,7,data(9,18,11,2021),data(16,18,11,2021),3).
entrega(12,6,4,6,data(14,1,10,2021),data(19,1,10,2021),4).
entrega(13,8,2,4,data(15,16,10,2021),data(19,16,10,2021),4).
entrega(14,6,3,6,data(13,26,9,2021),data(16,26,9,2021),3).
%entrega(15,11,1,1,data(9,3,9,2021),data(12,3,9,2021),3).
%entrega(16,7,4,4,data(8,1,10,2021),data(10,1,10,2021),2).
%entrega(17,10,5,1,data(14,14,10,2021),data(18,14,10,2021),4).
%entrega(18,9,2,9,data(16,8,11,2021),data(18,8,11,2021),4).
%entrega(19,10,4,4,data(13,24,10,2021),data(17,24,10,2021),4).
%entrega(20,1,1,4,data(9,25,11,2021),data(13,27,11,2021),3).

%Não entregues:
%entrega(15,11,1,1,data(9,3,9,2021),data(8,3,9,2021),3).
%entrega(16,7,4,4,data(8,1,10,2021),data(7,1,10,2021),2).
%entrega(17,10,5,1,data(14,14,10,2021),data(13,14,10,2021),4).
%entrega(18,9,2,9,data(16,8,11,2021),data(15,8,11,2021),4).
%entrega(19,10,4,4,data(13,24,10,2021),data(12,24,10,2021),4).
%entrega(20,1,1,4,data(9,25,11,2021),data(8,25,11,2021),3).



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

%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

%~~~~~~~~~~~~~~~~~~
% Queries
%~~~~~~~~~~~~~~~~~~

% Query 1. 
	%Identificar o estafeta que utilizou mais vezes um meio de transporte mais ecológico;
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

% Query 2. 
	%Identificar que estafetas entregaram determinada(s) encomenda(s) a um determinado cliente;

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


% Query 5. 
	%Identificar quais as zonas (e.g., rua ou freguesia) com maior volume de entregas por parte da Green Distribution;
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
createListaMorada([X|Tail],Temp,Result):- morada(X, Rua,_,_,_),
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

%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~%
%										Parte II										   %
%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~%

%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

%~~~~~~~~~~~~~~~~~~
% Queries
%~~~~~~~~~~~~~~~~~~

%Query 1.
	%CircuitoBFS
circuitoBfs1Delivery(Grafo,Dest,Path):-bfs(Grafo,armazem,Dest,Temp),
							  reverse(Temp,NewTemp),
							  tail(NewTemp,MissingTemp),
							  append(Temp,MissingTemp,Path).

	%CircuitoDFS
circuitoDfs1Delivery(Grafo,Dest,Path):-dfs(Grafo,armazem,Dest,Temp),
							  reverse(Temp,NewTemp),
							  tail(NewTemp,MissingTemp),
							  append(Temp,MissingTemp,Path).
%Query 2.
		%Aresta
aresta(Rua1,Rua2,Distancia):-morada(Id1,Rua1,Freguesia,X1,Y1),morada(Id2,Rua2,Freguesia,X2,Y2),Id1\==Id2,abs(Id2-Id1)=<2,
							distanciaPontos(X1,Y1,X2,Y2,Distancia).
aresta(Rua1,Rua2,Distancia):- morada(Id1,Rua1,Freguesia1,X1,Y1),morada(Id2,Rua2,Freguesia2,X2,Y2),Id1\=Id2,abs(Id2-Id1)=:=1,
							distanciaPontos(X1,Y1,X2,Y2,Distancia).

		%Auxiliar de listaArestasAux
listaArestasAux(X,[],Temp,Result):- X>0,
									morada(X,RuaX,_,Xx,Xy),
									distanciaPontos(41.205273,-8.530271,Xx, Xy,Dist),
									append([aresta(RuaX,armazem,Dist)],Temp,NewTemp),
									reverse(NewTemp,Result)
									;
									append([],Temp,NewTemp),
									reverse(NewTemp,Result).
listaArestasAux(X,[aresta(Rua1,Rua2,Dist)|Tail],Temp,Result):- 
											morada(Id1,Rua1,_,_,_),
											morada(Id2,Rua2,_,_,_),
										   \+member(aresta(Rua1,Rua2,Dist),Temp),\+member(aresta(Rua2,Rua1,Dist),Temp),
										   append([aresta(Rua1,Rua2,Dist)],Temp,NewTemp),
										   NewX is max(Id1,Id2),
										   listaArestasAux(NewX,Tail,NewTemp,Result)
										   ;
										   listaArestasAux(X,Tail,Temp,Result).

		%Lista das arestas do grafo
listaArestas(Result):-findall(aresta(Rua1,Rua2,Dist),aresta(Rua1,Rua2,Dist),Temp),listaArestasAux(0,Temp,[],Result).

		%Lista dos vertices do grafo
listaVertices(Result):- findall(Rua,morada(_,Rua,_,_,_),Result).

		%Criacao do Grafo
g(grafo(Vertices,Arestas)):- listaVertices(Vertices),listaArestas(Arestas).

%Query 3.	
	% Circuitos com maior número de entregas (por volume e peso).
mostByMetricAux(_,[],Temp,Result):-reverse(Temp,Result).
mostByMetricAux(Head,Lista,Temp,Result):-scndTList(Head,Lista,0,Rua/PesoT),
                                     append([Rua/PesoT],Temp,NewT),
                                     elimElem(Head,Lista,[],NewLista),
                                     head(NewLista,NewHead),
                                     mostByMetricAux(NewHead,NewLista,NewT,Result).

mostByMetric(peso,Result):- findall(Rua/Peso,(morada(IdMorada,Rua,_,_,_),entrega(Id,_,_,IdMorada,_,_,_),encomenda(Id,Peso,_)),Lista1),
                                  head(Lista1,Head),
                                  mostByMetricAux(Head,Lista1,[],Temp),
                                  maiorTuplo(Temp,Result).


mostByMetric(volume,Result):-findall(Rua/Volume,(morada(IdMorada,Rua,_,_,_),entrega(Id,_,_,IdMorada,_,_,_),encomenda(Id,_,Volume)),Lista1),
								  head(Lista1,Head),
                                  mostByMetricAux(Head,Lista1,[],Temp),
                                  maiorTuplo(Temp,Result).

%Query 4.
	

%Query 5.
	%Escolher o circuito mais rápido (usando o critério da distância)

fastestCircuitAAux(N,Rua,Lista,Custo,FinalLista/Custo):-N>2,
													tail(Lista,Tail),
								 					head(Tail,Rua2),
								 					distanciaRuas(Rua,Rua2,Distancia),
								 					NewCusto is 2*Custo-Distancia,
								 					reverse(Lista,NewLista),
								 					append(NewLista,Tail,FinalLista)
								 					;
								 					N=:=2,
								  					tail(Lista,Tail),
								  					NewCusto is 2*Custo,
								  					reverse(Lista,NewLista),
								  					append(NewLista,Tail,FinalLista).


fastestCircuitA(IdEntrega,Result):-entrega(IdEntrega,_,_,IdMorada,DataInicial,DataFinal,_),
								  dataMaior(DataFinal,DataInicial),
								  morada(IdMorada,Rua,_,_,_),
								  resolve_aestrela(Rua,Lista/Custo),
								  length(Lista,N),
								  fastestCircuitAAux(N,Rua,Lista,Custo,Result).
								  
%Query 6.
	%Escolher o circuito mais ecológico (usando um critério de tempo)
mostEcologicCircuit(IdEntrega,Result):-entrega(IdEntrega,_,_,IdMorada,DataInicial,DataFinal,_),
								  dataMaior(DataFinal,DataInicial),
								  encomenda(IdEntrega,Peso,_),
								  morada(IdMorada,Rua,_,X1,Y1),
								  estima(Rua,Estima).


%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

%~~~~~~~~~~~~~~~~~~
% Algoritmos de pesquisa
%~~~~~~~~~~~~~~~~~~

%Pesquisa não Informada:

	%Pesquisa Primeiro em Largura (Breadth-first search (bfs)).
	%Extensão do Predicado Bfs: Grafo, Origem, Destino, Caminho-> {V,F}.
bfs2(Grafo,Dest,[[Dest|Tail]|_],[Dest|Tail]).
bfs2(Grafo,Dest,[LA|Outros],Cam) :- LA=[Act|_],
                                    findall([X|LA], (Dest\==Act,adjacente(X,Act,Grafo),\+member(X,LA)), Novos),
                                    append(Outros,Novos,Todos),
                                    bfs2(Grafo,Dest,Todos,Cam).

bfs(Grafo,Orig,Dest,Cam) :- bfs2(Grafo,Orig,[[Dest]],Cam).


	%Pesquisa Primeiro em Profundidade (Depth-first search (dfs)).
	%%Extensão do Predicado Bfs: Grafo, Origem, Destino, Caminho-> {V,F}.
dfs2(G, A, B, T, [B]) :-
    head(T, B).

dfs2(G, A, B, Historico, [A|Caminho]) :-
    adjacente(A,Y,G),
    \+member(Y, Historico),
    dfs2(G, Y, B, [Y|Historico], Caminho).

dfs(G,Orig,B,Path):- dfs2(G,Orig,B,[Orig],Path).

	%Busca Iterativa Limitada em Profundidade. 										
	%Extensao do predicado ilProfjam: Grafo,Orig,Dest,Caminho ~> {V,F}  

ilProfjam2(G,A,[Y|P1],ListHldr,Max,Max,P):-NewXSave is NewMax+1 ,ilProfjam2(G,A,ListHldr,ListHldr,0,NewMax,P).
ilProfjam2(G,A,[A|P1],ListHldr,X,Max,[A|P1]).
%ilProfjam2(G,A,[Y|P1],ListHldr,X,Max,P) :- findall(adjacente(A,))

ilProfjam(Grafo,A,B,P) :- ilProfjam2(G,A,[B],[B],0,1,P).

%Pesquisa Informada:
	%Goal
goal(armazem).

	%Gulosa
resolve_gulosa(Nodo, Caminho/Custo) :-
	estima(Nodo, Estima),
	agulosa([[Nodo]/0/Estima], InvCaminho/Custo/_),
	inverso(InvCaminho, Caminho).

agulosa(Caminhos, Caminho) :-
	obtem_melhor_g(Caminhos, Caminho),
	Caminho = [Nodo|_]/_/_,
	goal(Nodo).

agulosa(Caminhos, SolucaoCaminho) :-
	obtem_melhor_g(Caminhos, MelhorCaminho),
	seleciona(MelhorCaminho, Caminhos, OutrosCaminhos),
	expande_gulosa(MelhorCaminho, ExpCaminhos),
	append(OutrosCaminhos, ExpCaminhos, NovoCaminhos),
    agulosa(NovoCaminhos, SolucaoCaminho).		

obtem_melhor_g([Caminho], Caminho) :- !.

obtem_melhor_g([Caminho1/Custo1/Est1,_/Custo2/Est2|Caminhos], MelhorCaminho) :-
	Est1 =< Est2, !,
	obtem_melhor_g([Caminho1/Custo1/Est1|Caminhos], MelhorCaminho).
	
obtem_melhor_g([_|Caminhos], MelhorCaminho) :- 
	obtem_melhor_g(Caminhos, MelhorCaminho).

expande_gulosa(Caminho, ExpCaminhos) :-
	findall(NovoCaminho, adjacente2(Caminho,NovoCaminho), ExpCaminhos).	

	
	%Algoritmo A*
resolve_aestrela(Nodo, Caminho/Custo) :-
	estima(Nodo, Estima),
	aestrela([[Nodo]/0/Estima], InvCaminho/Custo/_),
	inverso(InvCaminho, Caminho).

aestrela(Caminhos, Caminho) :-
	obtem_melhor(Caminhos, Caminho),
	Caminho = [Nodo|_]/_/_,
	goal(Nodo).

aestrela(Caminhos, SolucaoCaminho) :-
	obtem_melhor(Caminhos, MelhorCaminho),
	seleciona(MelhorCaminho, Caminhos, OutrosCaminhos),
	expande_aestrela(MelhorCaminho, ExpCaminhos),
	append(OutrosCaminhos, ExpCaminhos, NovoCaminhos),
    aestrela(NovoCaminhos, SolucaoCaminho).	

obtem_melhor([Caminho], Caminho) :- !.
obtem_melhor([Caminho1/Custo1/Est1,_/Custo2/Est2|Caminhos], MelhorCaminho) :-
	Custo1 + Est1 =< Custo2 + Est2, !,
	obtem_melhor([Caminho1/Custo1/Est1|Caminhos], MelhorCaminho). 
obtem_melhor([_|Caminhos], MelhorCaminho) :- 
	           obtem_melhor(Caminhos, MelhorCaminho).



expande_aestrela(Caminho, ExpCaminhos) :-
	findall(NovoCaminho, adjacente2(Caminho,NovoCaminho), ExpCaminhos).

adjacente2([Nodo|Caminho]/Custo/_, [ProxNodo,Nodo|Caminho]/NovoCusto/Est) :-
	aresta(Nodo, ProxNodo, PassoCusto),
	\+member(ProxNodo, Caminho),
	NovoCusto is Custo + PassoCusto,
	estima(ProxNodo, Est).

%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

%~~~~~~~~~~~~~~~~~~
% Auxiliares
%~~~~~~~~~~~~~~~~~~

	%Cabeça de uma lista
head([],0).
head([Result],Result).
head([Result|Tail],Result).
   	
   	%Cauda de uma lista
tail([H|Tail],Result):-append([],Tail,Result).

	%Distancia entre dois pontos
distanciaRuas(Rua1,Rua2,Distancia):-morada(_,Rua1,_,X1,Y1),morada(_,Rua2,_,X2,Y2),
									R is sqrt((X1-X2)^2 + (Y1-Y2)^2),
   	 								Distancia is R*100.

distanciaPontos(X1,Y1,X2,Y2,Distancia):-R is sqrt((X1-X2)^2 + (Y1-Y2)^2),
   	 									Distancia is R*100.

  	%Velocidade real de um veiculo tendo em consideração o peso transportado
trueSpeed(bicicleta,Weight,Vfinal):- Vfinal is 10-(0.7*Weight).
trueSpeed(mota,Weight,Vfinal):-Vfinal is 35-(0.5*Weight).
trueSpeed(carro,Weight,Vfinal):- Vfinal is 25-(0.1*Weight).
	
	%Tempo de entrega tendo em consideração a distancia e a velociade real
effDeliveryTime(TrueSpeed,Distance,EffTime):- EffTime is Distance/TrueSpeed.

	%Extensao do predicado adjacente : Id1, Id2, Grafo -> {V, F, D}
adjacente(X,Y, grafo(_,Arestas)) :- member(aresta(X,Y,Dist),Arestas).
adjacente(X,Y, grafo(_,Arestas)) :- member(aresta(Y,X,Dist),Arestas).


	%Elimina todas as ocorrências de um elemento de uma lista
elimElem(_,[],Temp,Result):- reverse(Temp,Result).
elimElem(X/_,[H/Peso|T],Temp,Result):- X == H , 
                            elimElem(X/_,T,Temp,Result)
                            ;
                            X\==H,
                            append([H/Peso],Temp,NewR),
                            elimElem(X/_,T,NewR,Result).

	%Devolve tuplos, com apenas uma ocorrência e o 2ºtuplo acumulado
scndTList(Rua/_,[],PM, Rua/PM).
scndTList(Rua/_,[Rua1/Metrica|T],PM,Result):- Rua\== Rua1,
                                        scndTList(Rua/_,T,PM,Result)
                                        ;
                                        Rua==Rua1,
                                        NewPM is PM+Metrica,
                                        scndTList(Rua/_,T,NewPM,Result).
    %Auxiliar a maiorTuplo
maiorTuploAux(Result,[],Result).
maiorTuploAux(Rua1/Q1,[Rua2/Q2|T],Result):- Q1>=Q2,
                                            maiorTuploAux(Rua1/Q1,T,Result)
                                            ;
                                            Q1<Q2,
                                            maiorTuploAux(Rua2/Q2,T,Result).

    %Maior tupolo de uma lista
maiorTuplo([H|T],Result):- maiorTuploAux(H,T,Result).

	%Inverte uma lista
inverso(Xs, Ys):-
	inverso(Xs, [], Ys).


inverso([], Xs, Xs).
inverso([X|Xs],Ys, Zs):-
	inverso(Xs, [X|Ys], Zs).

	%Seleciona 
seleciona(E, [E|Xs], Xs).
seleciona(E, [X|Xs], [X|Ys]) :- seleciona(E, Xs, Ys).

	%Estima a distancia de uma rua ao armazem
estima(Rua2,Result):-morada(_,armazem,_,X1,Y1),morada(_,Rua2,_,X2,Y2),
						  distanciaPontos(X1,Y1,X2,Y2,Result).

	%Soma de horas com uma data.
hourDateSum(Hour,data(H,D,M,A),data(HF,DF,MF,AF)):-
									  date_time_stamp(date(A,M,D,H,0,0,_,_,_),Stamp),
									  NewStamp is Stamp+(1+Hour)*3600,
									  stamp_date_time(NewStamp, Date,'UTC'),
									  date_time_value(hour, Date, HF),
									  date_time_value(day, Date, DF),
									  date_time_value(month, Date, MF),
									  date_time_value(year, Date, AF).
									  
