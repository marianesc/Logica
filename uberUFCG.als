module uberUFCG

abstract sig Usuario {
	status: lone Status
}
sig Passageiro in Usuario {}
sig Motorista in Usuario {}

abstract sig Status {}
one sig DEBITO, CREDITO extends Status {}

abstract sig Corrida {
	passageiros: some Passageiro,
	motorista: one Motorista
}

sig Ida extends Corrida {
	regiaoOrigem: one Regiao,
	horario: one HorarioIda
}

sig Volta extends Corrida {
	regiaoDestino: one Regiao,
	horario: one HorarioVolta
}

abstract sig Regiao {}
one sig CENTRO, NORTE, SUL, LESTE, OESTE extends Regiao {}

abstract sig HorarioIda {}
one sig H7MIN30, H9MIN30, H13MIN30, H15MIN30 extends HorarioIda {}

abstract sig HorarioVolta {}
one sig H10MIN00, H12MIN00, H16MIN00, H18MIN00 extends HorarioVolta {}

fact RegrasCorrida {
-- Toda corrida precisa ter no máximo 3 passageiros
	all c: Corrida | maxPassageiros[c] 

-- Qualquer passageiro só pode estar em no máximo uma ida
	all p: Passageiro | apenasUmaCorridaIda[p] 

-- Qualquer passageiro só pode estar em no máximo uma volta
	all p: Passageiro | apenasUmaCorridaVolta[p]

-- Um mesmo usuário não pode ser simultaneamente motorista e passageiro
	all c: Corrida | ouMotoristaOuPassageiro[c]

-- Corridas diferentes no mesmo horário, não podem ter usuários em comum
	all disj i1, i2 : Ida |  ouMotoristaOuPassageiroMesmoHorario[i1, i2]
	all disj v1, v2 : Volta |  ouMotoristaOuPassageiroMesmoHorario[v1, v2]

--Contabilidade para saber se o usurário está com credito ou débito em corridas
	all u: Usuario | contabilidade[u]

--Todo usuário precisa participar de pelo menos uma corrida.
	all u: Usuario | #u.~passageiros >= 1 or #u.~motorista >= 1
}

pred maxPassageiros[c: Corrida] {
	#c.passageiros <= 3
}

pred apenasUmaCorridaIda[p: Passageiro] {
	#((p.~passageiros) & Ida) <= 1
}

pred apenasUmaCorridaVolta[p: Passageiro] {
	#((p.~passageiros) & Volta) <= 1
}

pred ouMotoristaOuPassageiro[c: Corrida] {
	#(c.motorista & c.passageiros) = 0
}

pred ouMotoristaOuPassageiroMesmoHorario[i1, i2 : Ida] {
	 (i1.horario = i2.horario) implies #(usuariosDaCorrida[i1] &  usuariosDaCorrida[i2]) = 0
}

pred ouMotoristaOuPassageiroMesmoHorario[v1, v2 : Volta] {
	 (v1.horario = v2.horario) implies #(usuariosDaCorrida[v1] &  usuariosDaCorrida[v2]) = 0
}

pred contabilidade[u: Usuario] {
	(#u.~passageiros > #u.~motorista) implies u.status = DEBITO
	(#u.~passageiros < #u.~motorista) implies u.status = CREDITO
	(#u.~passageiros = #u.~motorista) implies no u.status
}

fun usuariosDaCorrida[c: Corrida]: set Usuario {
	c.motorista + c.passageiros
}

pred show []{}
run show for 5
