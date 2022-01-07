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
cliente(1,[2,4,51,59,72,79,85]).
cliente(2,[5,41,50,52,65]).
cliente(3,[1,9,56,61,69,80,82]).
cliente(4,[3,6,42,47,76,89]).
cliente(5,[7,8,10,58,71,84]).
cliente(6,[12,14,55,68,73,81]).
cliente(7,[11,16,40,46,54,60,75,86,91]).
cliente(8,[13,43,48,53,64,77,90]).
cliente(9,[18,44,49,62,67,74]).
cliente(10,[17,19,57,70,78,83,87,93]).
cliente(11,[15,20,45,63,66,88,92]).

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
				%Adicionadas.
morada(11,ruaDaRocha,caminha,41.881815,-8.816272).
morada(12,ruaDoRovial,caminha,41.848053,-8.853980).
morada(13,ruaDoRouxico,caminha,41.844075,-8.866999).
morada(14,ruaDoRoncal,caminha,41.905238,-8.799445).
morada(15,ruaCentralDaEscola,amarante,41.278119,-8.058343).
morada(16,ruaDaPortela,amarante,41.260217,-8.086627).
morada(17,ruaDaTapada,amarante,41.290806,-8.103075).
morada(18,ruaDoForcado,amarante,41.316165,-8.114792).
morada(19,ruaDoPomar,amarante,41.280452,-8.207678).
morada(20,ruaDaRelvinha,leiria,39.788730,-8.748457).
morada(21,ruaDaResil,leiria,39.829484,-8.726387).
morada(22,ruaDaRosa,leiria,39.812974,-8.752830).
morada(23,ruaDoRibeiro,leiria,39.776065,-8.822998).
morada(24,ruaDasFontainhas,lamego,41.101168,-7.814401).
morada(25,ruaDaMazeda,lamego,41.094981,-7.810395).
morada(26,ruaDasCortes,lamego,41.099345,-7.812701).
morada(27,ruaDoTeatro,lamego,41.096807,-7.811070).
morada(28,ruaDoCastelo,lamego,41.098376,-7.810755).
morada(29,ruaTabaleao,tondela,40.513672,-8.092147).
morada(30,ruaDaCal,tondela,40.588022,-8.031365).
morada(31,ruaDaFraga,tondela,40.504475,-7.990560).
morada(32,ruaAltoBairro,tondela,40.536921,-8.084464).
morada(33,ruaDoMeal,tondela,40.491108,-8.093568).
morada(34,ruaDoSol,amadora,38.744130,-9.217829).
morada(35,ruaSantoAntonio,amadora,38.756414,-9.241912).
morada(36,ruaDomDinis,amadora,38.752439,-9.233433).
morada(37,ruaDiasCoelho,amadora,38.768951,-9.217987).
morada(38,ruaFernaoLopes,amadora,38.757007,-9.212166).


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
%___
entrega(40,7,2,11,data(10,10,11,2021),data(12,10,11,2021),3).
entrega(41,7,3,11,data(9,18,6,2021),data(16,18,6,2021),3).
entrega(42,4,4,12,data(10,11,7,2021),data(13,11,7,2021),5).
entrega(43,8,5,12,data(8,16,5,2021),data(11,16,5,2021),4).
entrega(44,7,1,13,data(8,1,4,2021),data(10,1,4,2021),2).
entrega(45,7,1,13,data(2,18,11,2021),data(5,10,11,2021),3).
entrega(46,7,2,14,data(8,18,6,2021),data(14,18,6,2021),3).
entrega(47,4,3,14,data(10,11,7,2021),data(18,11,7,2021),5).
entrega(48,8,4,15,data(8,16,5,2021),data(9,16,5,2021),4).
entrega(49,7,5,15,data(11,1,4,2021),data(22,1,4,2021),2).
entrega(50,7,2,16,data(2,18,11,2021),data(5,10,11,2021),3).
entrega(51,7,3,16,data(8,18,6,2021),data(14,18,6,2021),3).
entrega(52,4,1,17,data(10,11,7,2021),data(18,11,7,2021),5).
entrega(53,8,4,17,data(8,16,5,2021),data(9,16,5,2021),4).
entrega(54,7,5,18,data(11,1,4,2021),data(22,1,4,2021),2).
entrega(55,6,4,18,data(16,1,2,2021),data(19,1,2,2021),4).
entrega(56,3,5,19,data(9,31,9,2021),data(21,31,9,2021),4).
entrega(57,10,4,19,data(13,24,10,2021),data(17,24,10,2021),4).
entrega(58,5,2,20,data(14,23,11,2021),data(21,23,11,2021),3).
entrega(59,1,2,20,data(12,22,11,2021),data(20,22,11,2021),2).
entrega(60,7,1,21,data(2,1,7,2021),data(4,1,7,2021),2).
entrega(61,7,1,21,data(15,12,12,2021),data(17,12,12,2021),3).
entrega(62,7,2,22,data(8,18,6,2021),data(14,18,6,2021),3).
entrega(63,4,3,22,data(10,11,7,2021),data(18,11,7,2021),5).
entrega(64,8,4,23,data(8,16,5,2021),data(9,16,5,2021),4).
entrega(65,7,5,23,data(11,1,4,2021),data(17,1,4,2021),2).
entrega(66,7,2,24,data(3,18,1,2021),data(5,10,1,2021),3).
entrega(67,7,3,24,data(9,11,11,2021),data(14,11,11,2021),3).

entrega(68,6,1,25,data(3,5,4,2021),data(7,5,4,2021),4).
entrega(69,3,2,25,data(19,21,1,2021),data(21,21,1,2021),4).
entrega(70,10,3,26,data(13,22,2,2021),data(17,22,2,2021),4).
entrega(71,5,4,26,data(14,9,9,2021),data(19,9,9,2021),3).
entrega(72,1,2,27,data(22,22,11,2021),data(23,22,11,2021),2).
entrega(73,7,5,27,data(2,8,9,2021),data(4,8,9,2021),2).
entrega(74,7,5,28,data(15,12,12,2021),data(17,12,12,2021),3).
entrega(75,7,2,28,data(18,8,6,2021),data(20,8,6,2021),3).
entrega(76,4,3,29,data(10,1,9,2021),data(18,1,9,2021),5).
entrega(77,8,4,29,data(8,16,5,2021),data(9,16,5,2021),4).
entrega(78,7,3,30,data(11,1,4,2021),data(17,1,4,2021),2).
entrega(79,7,2,30,data(3,18,1,2021),data(5,10,1,2021),3). 

entrega(80,3,1,31,data(9,11,11,2021),data(14,11,11,2021),3).
entrega(81,6,2,31,data(3,5,4,2021),data(7,5,4,2021),4).
entrega(82,3,3,32,data(19,21,1,2021),data(21,21,1,2021),4).
entrega(83,10,3,32,data(13,22,2,2021),data(17,22,2,2021),4).
entrega(84,5,4,33,data(12,19,4,2021),data(17,19,4,2021),3).
entrega(85,1,2,34,data(22,22,11,2021),data(23,22,11,2021),2).
entrega(86,7,1,34,data(2,8,9,2021),data(4,8,9,2021),2).
entrega(87,10,5,35,data(15,2,2,2021),data(17,2,2,2021),3).
entrega(88,11,2,35,data(12,8,1,2021),data(20,8,1,2021),3).
entrega(89,4,3,36,data(10,1,9,2021),data(18,1,9,2021),5).
entrega(90,8,1,37,data(8,16,5,2021),data(9,16,5,2021),4).
entrega(91,7,3,37,data(11,1,4,2021),data(17,1,4,2021),2).
entrega(92,11,3,38,data(13,20,12,2021),data(15,20,12,2021),3).
entrega(93,10,1,38,data(10,7,11,2021),data(14,7,11,2021),3).




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

encomenda(40,7,14).
encomenda(41,20,40).
encomenda(42,5,10).
encomenda(43,18,36).
encomenda(44,100,200).
encomenda(45,34,68).
encomenda(46,71,142).
encomenda(47,2,4).
encomenda(48,77,154).
encomenda(49,3,6).
encomenda(50,15,30).
encomenda(51,11,22).
encomenda(52,20,40).
encomenda(53,5,10).
encomenda(54,18,36).
encomenda(55,100,200).
encomenda(56,34,68).
encomenda(57,71,142).
encomenda(58,2,4).
encomenda(59,77,154).
encomenda(60,3,6).
encomenda(61,15,30).
encomenda(62,11,22).
encomenda(63,5,10).
encomenda(64,22,44).
encomenda(65,24,48).
encomenda(66,19,38).
encomenda(67,1,2).
encomenda(68,4,8).
encomenda(69,75,150).
encomenda(70,7,14).
encomenda(71,20,40).
encomenda(72,5,10).
encomenda(73,18,36).
encomenda(74,100,200).
encomenda(75,34,68).
encomenda(76,71,142).
encomenda(77,2,4).
encomenda(78,77,154).
encomenda(79,3,6).
encomenda(80,15,30).
encomenda(81,11,22).
encomenda(82,20,40).
encomenda(83,5,10).
encomenda(84,22,44).
encomenda(85,24,48).
encomenda(86,19,38).
encomenda(87,1,2).
encomenda(88,4,8).
encomenda(89,75,150).
encomenda(90,7,14).
encomenda(91,20,40).
encomenda(92,5,10).
encomenda(93,18,36).

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

precoServico(40,1,mota,36,55).
precoServico(41,4,mota,24,37).
precoServico(42,1,bicicleta,71,85).               
precoServico(43,2.5,mota,110,115).
precoServico(44,3,carro,51,71).                    
precoServico(45,0.5,carro,72,96).
precoServico(46,5,carro,2,19).
precoServico(47,5,bicicleta,15,23).
precoServico(48,6,carro,15,33).
precoServico(49,7,bicicleta,22,30).
precoServico(50,1,mota,36,55).
precoServico(51,4,mota,24,37).
precoServico(52,1,bicicleta,71,85).               
precoServico(53,2.5,mota,110,115).
precoServico(54,3,carro,51,71).                   
precoServico(55,0.5,carro,72,96).
precoServico(56,5,carro,2,19).
precoServico(57,5,bicicleta,15,23).
precoServico(58,6,carro,15,33).
precoServico(59,7,bicicleta,22,30).
precoServico(60,1,mota,36,55).
precoServico(61,4,mota,24,37).
precoServico(62,1,bicicleta,71,85).               
precoServico(63,2.5,mota,110,115).
precoServico(64,3,carro,51,71).                    
precoServico(65,0.5,carro,72,96).
precoServico(66,5,carro,2,19).
precoServico(67,5,bicicleta,15,23).
precoServico(68,6,carro,15,33).
precoServico(69,7,bicicleta,22,30).
precoServico(70,1,mota,36,55).
precoServico(71,4,mota,24,37).
precoServico(72,1,bicicleta,71,85).                
precoServico(73,2.5,mota,110,115).
precoServico(74,3,carro,51,71).                    
precoServico(75,0.5,carro,72,96).
precoServico(76,5,carro,2,19).
precoServico(77,5,bicicleta,15,23).
precoServico(78,6,carro,15,33).
precoServico(79,7,bicicleta,22,30).
precoServico(80,1,mota,36,55).
precoServico(81,4,mota,24,37).
precoServico(82,1,bicicleta,71,85).                
precoServico(83,2.5,mota,110,115).
precoServico(84,3,carro,51,71).                    
precoServico(85,0.5,carro,72,96).
precoServico(86,5,carro,2,19).
precoServico(87,5,bicicleta,15,23).
precoServico(88,6,carro,15,33).
precoServico(89,7,bicicleta,22,30).
precoServico(90,1,mota,36,55).
precoServico(91,6,carro,15,33).
precoServico(92,7,bicicleta,22,30).
precoServico(93,1,mota,36,55).

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

fastestCircuitG(IdEntrega,Result):-entrega(IdEntrega,_,_,IdMorada,DataInicial,DataFinal,_),
								  dataMaior(DataFinal,DataInicial),
								  morada(IdMorada,Rua,_,_,_),
								  resolve_gulosa(Rua,Lista/Custo),
								  length(Lista,N),
								  fastestCircuitAAux(N,Rua,Lista,Custo,Result).
								  								  
%Query 6.
	%Escolher o circuito mais ecológico (usando um critério de tempo)
mostEcologicCircuit(IdEntrega,Result):-entrega(IdEntrega,_,_,IdMorada,DataInicial,DataFinal,_),
								  dataMaior(DataFinal,DataInicial),
								  encomenda(IdEntrega,Peso,_),
								  morada(IdMorada,Rua,_,X1,Y1),
								  estima(Rua,Estima),
								 custoDerivadoTransport(Estima,Peso,DataInicial,DataFinal,Temp),
								 Result is 1. %% só para compilar o resto.


custoDerivadoTransport(DistE,Peso,DataInicial,DataFinal,Result):-trueSpeed(bicicleta,Peso,VBicicleta),
																 VBicicleta >0,
																 effDeliveryTime(VBicicleta,DistE,TimeBicicleta),
																 hourDateSum(TimeBicicleta,DataInicial,DataFinalE),
																 dataCompreendida(DataInicial,DataFinalE,DataFinal).

%sadge :C




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
									  
