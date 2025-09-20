/**
 * Projeto Lógica para Computação 2025.1
 * Tema 9: Sistema de Desenvolvimento de Software
 *
 * Grupo:
 * - Raissa Tainá Pordeus Ferreira (Salatiel)
 * - Ana Larissa Costa dos Santos (Salatiel)
 * - Maria Eduarda Ramos Lucena Maia (Massoni)
 * - Moisés Rodrigues Barbalho Filho (Massoni)
 */


// ========== DEFINIÇÃO DAS ENTIDADES PRINCIPAIS DO SISTEMA ==========

abstract sig Equipe {
    trabalhaEm: one Modulo // uma equipe pode trabalhar em um Módulo por vez
}
sig EquipeDev extends Equipe {}
one sig EquipeTeste extends Equipe {}

sig Modulo {
    versoes: some Versao,
    versaoPronta: one ProntaParaTestes,
    estado: one Estado
}

sig Versao {}

sig ProntaParaTestes in Versao {}

// ========== DEFINIÇÃO DOS ESTADOS POSSÍVEIS PARA UM MÓDULO ==========

abstract sig Estado {
    proximo: lone Estado // apontador para o próximo estado no ciclo
}
one sig EmDesenvolvimento, EmTestes, Integrado, Entregue extends Estado {}

// ========== FATOS E REGRAS DO SISTEMA ==========

fact EstruturaDasEquipes {
    #EquipeDev = 2
    #EquipeTeste = 1
}

fact ConsistenciaDasVersoes {
    all m: Modulo | m.versaoPronta in m.versoes
    all v: Versao | one m: Modulo | v in m.versoes
}

fact RegrasDeTrabalho {
    // 1. Equipes de desenvolvimento só trabalham em módulos com estado "EmDesenvolvimento".
    all dev: EquipeDev, m: dev.trabalhaEm | m.estado = EmDesenvolvimento

    // 2. A equipe de teste só trabalha em módulos com estado "EmTestes".
    all teste: EquipeTeste, m: teste.trabalhaEm | m.estado = EmTestes

    // 3. Duas equipes de desenvolvimento distintas nunca trabalham nos mesmos módulos.
    // Para todas as duplas de equipes de dev d1 e d2, se d1 for diferente de d2,
    // a interseção dos módulos em que trabalham deve ser vazia.
    all d1, d2: EquipeDev | d1 != d2 => no d1.trabalhaEm & d2.trabalhaEm

    // 4. Módulos em desenvolvimento devem ter pelo menos uma equipe de dev trabalhando neles
    all m: Modulo | m.estado = EmDesenvolvimento => some dev: EquipeDev | m in dev.trabalhaEm

    // 5. Módulos em teste devem ter a equipe de teste trabalhando neles
    all m: Modulo | m.estado = EmTestes => some teste: EquipeTeste | m in teste.trabalhaEm

  // Nenhuma equipe (dev ou teste) pode trabalhar em módulos entregues
   all e: Equipe | e.trabalhaEm.estado != Entregue
}

// ========== CICLO DE VIDA DAS VERSÕES (TRANSICOES) ==========

fact SequenciaEstados {
    EmDesenvolvimento.proximo = EmTestes
    EmTestes.proximo = Integrado
    Integrado.proximo = Entregue
    Entregue.proximo = none
}

// ========== VERIFICAÇÃO DE PROPRIEDADES (ASSERÇÕES) ==========

// 1. Toda versão pertence a exatamente um módulo
assert VersaoUnicaPorModulo {
    all v: Versao | one m: Modulo | v in m.versoes 
}
check VersaoUnicaPorModulo for 5

// 2. Todo módulo tem exatamente uma versão pronta para testes, 
//    e ela pertence às suas versões
assert VersaoPronta {
    all m: Modulo | one m.versaoPronta and m.versaoPronta in m.versoes
}
check VersaoPronta for 5

// 3. Equipes de dev só trabalham em módulos em desenvolvimento
assert DevsSoEmDesenvolvimento {
    all dev: EquipeDev | dev.trabalhaEm.estado = EmDesenvolvimento
}
check DevsSoEmDesenvolvimento for 5

// 4. Todo módulo em desenvolvimento tem pelo menos uma equipe de dev
assert DesenvolvimentoImplicaEquipeDev {
    all m: Modulo | m.estado = EmDesenvolvimento => some dev: EquipeDev | m in dev.trabalhaEm
}
check DesenvolvimentoImplicaEquipeDev for 5

// 5. A equipe de teste só trabalha em módulos em testes
assert TesteSoEmTestes {
    all t: EquipeTeste | t.trabalhaEm.estado = EmTestes
}
check TesteSoEmTestes for 5

// 6. Todo módulo em testes tem a equipe de teste
assert ModuloEmTestesTemEquipeDeTeste {
    all m: Modulo | m.estado = EmTestes => some t: EquipeTeste | m in t.trabalhaEm
}
check ModuloEmTestesTemEquipeDeTeste for 5

// 7. Duas equipes de desenvolvimento distintas nunca trabalham no mesmo módulo
assert EquipesDevDistintasNaoCompartilhamModulos {
    all d1, d2: EquipeDev | d1 != d2 => no d1.trabalhaEm & d2.trabalhaEm
}
check EquipesDevDistintasNaoCompartilhamModulos for 5

// 8. Nenhuma equipe deve trabalhar em módulos entregues
assert NenhumaEquipeEmModuloEntregue {
    all e: Equipe | e.trabalhaEm.estado != Entregue
}

check NenhumaEquipeEmModuloEntregue for 5


// 9. Todo estado diferente de Entregue deve ter próximo estado definido
assert TodoEstadoNaoEntregueTemProximo {
    no s: Estado - Entregue | s.proximo = none
}
check TodoEstadoNaoEntregueTemProximo for 5

// 10. Nenhum módulo pode ter estado inválido (ou seja, estado que não está na sequência)
assert NenhumModuloComEstadoInvalido {
    no m: Modulo | m.estado not in EmDesenvolvimento + EmTestes + Integrado + Entregue
}
check NenhumModuloComEstadoInvalido for 5 but 15 Versao

// 11. Módulos Entregues não devem ter próximo estado
assert ModulosEntreguesSemProximo {
    no m: Modulo | m.estado = Entregue and m.estado.proximo != none
}
check ModulosEntreguesSemProximo for 5 but 15 Versao


// ========== CENÁRIO DE EXEMPLO PARA VISUALIZAÇÃO ==========

pred CenarioExemplo {
    some m1, m2, m3, m4, m5: Modulo {
        m1 != m2 and m1 != m3 and m1 != m4 and m1 != m5 and
        m2 != m3 and m2 != m4 and m2 != m5 and
        m3 != m4 and m3 != m5 and
        m4 != m5

        // Equipes de desenvolvimento
        one d1, d2: EquipeDev {
            d1 != d2
            d1.trabalhaEm = m1
            d2.trabalhaEm = m2

            m1.estado = EmDesenvolvimento
            m2.estado = EmDesenvolvimento
        }

        // Equipe de teste
        one t1: EquipeTeste {
            t1.trabalhaEm = m3
            m3.estado = EmTestes
        }

        // Módulos sem equipe trabalhando
        m4.estado = Integrado
        m5.estado = Entregue
    }
}

run CenarioExemplo for 5 but 15 Versao 
