/**
 * Projeto Lógica para Computação 2025.1
 * Tema 9: Sistema de Desenvolvimento de Software
 *
 * Grupo:
 * - Raissa Tainá Pordeus Ferreira
 * - Ana Larissa
 * - Eduarda Maia
 * - Moisés Barbalho
 */

// ========== DEFINIÇÃO DOS ESTADOS POSSÍVEIS PARA UM MÓDULO ==========

abstract sig Estado {}
one sig EmDesenvolvimento, EmTestes, Integrado, Entregue extends Estado {}

// ========== DEFINIÇÃO DAS ENTIDADES PRINCIPAIS DO SISTEMA ==========

// Uma Equipe pode trabalhar em um ou mais Módulos.
sig Equipe {
    trabalhaEm: set Modulo
}

// Existem dois tipos de equipes, que são subconjuntos de Equipe.
sig EquipeDev in Equipe {}
sig EquipeTeste in Equipe {}

// Um Módulo do sistema.
sig Modulo {
    versoes: some Versao,
    prontaParaTeste: one Versao,
    estado: one Estado
}
sig Versao {
    moduloPai: one Modulo
}


// ========== FATOS E REGRAS DO SISTEMA ==========

fact EstruturaDasEquipes {
    #EquipeDev = 2
    #EquipeTeste = 1
    no EquipeDev & EquipeTeste
}

fact ConsistenciaDasVersoes {
    all m: Modulo | m.prontaParaTeste in m.versoes
    all v: Versao | v in v.moduloPai.versoes
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
}


// ========== VERIFICAÇÃO DE PROPRIEDADES (ASSERÇÕES) ==========

assert TesteImplicaNaoDesenvolvimento {
    all m: Modulo | m.estado = EmTestes => no dev: EquipeDev | m in dev.trabalhaEm
}

check TesteImplicaNaoDesenvolvimento for 5

assert DesenvolvimentoImplicaEquipeDev {
    all m: Modulo | m.estado = EmDesenvolvimento => some dev: EquipeDev | m in dev.trabalhaEm
}

check DesenvolvimentoImplicaEquipeDev for 5

assert EquipesDevDistintasNaoCompartilhamModulos {
    all d1, d2: EquipeDev | d1 != d2 => no d1.trabalhaEm & d2.trabalhaEm
}

check EquipesDevDistintasNaoCompartilhamModulos for 5



// ========== CENÁRIO DE EXEMPLO PARA VISUALIZAÇÃO ==========


pred CenarioExemplo {
    some m1, m2, m3, m4: Modulo {
        m1 != m2 and m1 != m3 and m1 != m4 and
        m2 != m3 and m2 != m4 and
        m3 != m4

        one d1, d2: EquipeDev {
            d1 != d2
            d1.trabalhaEm = m1
            d2.trabalhaEm = m2


            m1.estado = EmDesenvolvimento
            m2.estado = EmDesenvolvimento
        }


        one t1: EquipeTeste {
            // T1 trabalha em m3.
            t1.trabalhaEm = m3
            // m3 está em testes.
            m3.estado = EmTestes
        }

        m4.estado = Entregue
        no Equipe.trabalhaEm & m4
    }
}

run CenarioExemplo for 5