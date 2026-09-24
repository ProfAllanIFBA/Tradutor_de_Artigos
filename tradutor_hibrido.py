"""Tradutor local em massa v8.8.0.

O uso normal é feito por ``traduzir_pasta``. Os PDFs da pasta de entrada são
processados em sequência e recebem a tradução em comentários. Nenhum texto é
enviado a serviços de tradução: depois da preparação inicial do modelo, toda a
inferência funciona localmente em CPU ou GPU CUDA.

Modelos disponíveis:
    nllb_1_3b  melhor equilíbrio entre qualidade e velocidade (recomendado)
    nllb_600m  mais rápido e econômico em memória
    argos      mais leve; pode usar inglês como idioma intermediário

O programa detecta o idioma de cada trecho, preserva o que já estiver em
português, referências e elementos técnicos, recupera respostas incompletas,
reconstrói blocos contíguos e continua o lote se um fragmento ou arquivo falhar.
"""
__version__ = "8.8.0"

# Conjunto inicial para artigos acadêmicos do usuário. No notebook, a lista
# pode ser reduzida ou ampliada sem alterar este módulo.
DEFAULT_MIXED_LANGUAGES = ("fr", "en", "it", "es", "pt")

import re
import math
import zipfile
from pathlib import PurePosixPath
from datetime import datetime, timezone
import json
import time
import hashlib
import statistics
import threading
import random
import os
import sys
import shutil
import subprocess
import tempfile
import threading as _threading
import http.server
import functools
import urllib.parse as _urlparse
import urllib.request as _urlrequest
from pathlib import Path

try:
    import pymupdf as fitz  # PyMuPDF moderno
except ImportError:
    import fitz  # compatibilidade com instalações antigas

# Transporte HTTP somente com a biblioteca padrão do Python.
import urllib.parse
import urllib.request
import urllib.error

# ============================================================
# CONFIGURAÇÃO
# ============================================================
INPUT_PDF = "doc.pdf"
OUTPUT_PDF = "doc_traduzido_com_comentarios.pdf"

SOURCE_LANG = "auto"  # usado apenas pelo modo de execução direta
TARGET_LANG = "pt"

# O comentário fica associado ao próprio realce.
# Em Adobe Acrobat / Foxit, ele aparece no painel de comentários.
# Traduções concluídas: realce claro e bastante transparente.
TRANSLATED_HIGHLIGHT_COLOR = (1.0, 0.96, 0.55)
TRANSLATED_HIGHLIGHT_OPACITY = 0.13

# Trechos que continuarem sem tradução após todas as tentativas:
# realce vermelho, mais visível, para localização imediata no PDF.
FAILED_HIGHLIGHT_COLOR = (1.0, 0.25, 0.25)
FAILED_HIGHLIGHT_OPACITY = 0.30
FAILED_COMMENT_TEXT = "Trecho sem tradução após múltiplas tentativas."

COMMENT_AUTHOR = "Tradução automática"
COMMENT_SUBJECT = "Tradução automática"

# Se True, além do realce cria um ícone de comentário.
# Normalmente deixe False para não duplicar itens no painel lateral.
ADD_STICKY_NOTE = False
STICKY_NOTE_ICON = "Comment"

# Tradução: o controle vale também para chamadas antigas com modo="rapido".
MAX_CHARS_PER_REQUEST = 3500
MAX_CHARS_PER_UNIT = 1200
FAST_MODE_WORKERS = 1
TRANSLATION_ENGINE = "auto"
TRANSLATION_TIMEOUT_SECONDS = 25

# Extração / agrupamento
MIN_ALPHA_CHARS = 3
HEADER_FOOTER_ZONE = 0.10       # 10% superior e inferior
REPEATED_MARGIN_MIN_RATIO = 0.25
REPEATED_MARGIN_MIN_PAGES = 3

# Para testar só parte do artigo:
START_PAGE = 1                  # 1 = primeira página
END_PAGE = None                # None = até o fim

# Extração por Chrome (fallback para PDFs escaneados)
# "auto": usa PyMuPDF quando houver texto e Chrome quando a página for imagem.
# "nativo": nunca abre Chrome.
# "chrome": usa o Chrome para as páginas sem camada textual útil.
TEXT_EXTRACTION_ENGINE = "nativo"
CHROME_OCR_TIMEOUT_SECONDS = 120
CHROME_OCR_POLL_SECONDS = 2.0
CHROME_MIN_ALPHA_PER_PAGE = 35
CHROME_LOCAL_PROFILE_DIRNAME = ".tradutor_chrome_profile"
CHROME_LOCAL_DEPS_DIRNAME = ".tradutor_chrome_deps"


# ============================================================
# UTILITÁRIOS DE TEXTO
# ============================================================
def normalize_spaces(text: str) -> str:
    text = text.replace("\u00ad", "")  # soft hyphen
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r"\s*\n\s*", "\n", text)
    return text.strip()


# Trocas deliberadamente conservadoras: apenas formas inequivocamente
# lusitanas ou diferenças ortográficas usuais em textos acadêmicos.
_PT_BR_WORDS = {
    "acção": "ação", "acções": "ações",
    "actividade": "atividade", "actividades": "atividades",
    "actualmente": "atualmente",
    "actualização": "atualização", "actualizações": "atualizações",
    "actualizada": "atualizada", "actualizadas": "atualizadas",
    "actualizado": "atualizado", "actualizados": "atualizados",
    "adidactica": "adidática", "adidacticas": "adidáticas",
    "adidactico": "adidático", "adidacticos": "adidáticos",
    "adidáctica": "adidática", "adidácticas": "adidáticas",
    "adidáctico": "adidático", "adidácticos": "adidáticos",
    "adopção": "adoção", "adopções": "adoções",
    "académica": "acadêmica", "académicas": "acadêmicas",
    "académico": "acadêmico", "académicos": "acadêmicos",
    "antónimo": "antônimo", "antónimos": "antônimos",
    "aspeto": "aspecto", "aspetos": "aspectos",
    "autónoma": "autônoma", "autónomas": "autônomas",
    "autónomo": "autônomo", "autónomos": "autônomos",
    "binómio": "binômio", "binómios": "binômios",
    "carácter": "caráter", "carácteres": "caracteres",
    "conceção": "concepção", "conceções": "concepções",
    "conceptual": "conceitual", "conceptuais": "conceituais",
    "contacto": "contato", "contactos": "contatos",
    "controlo": "controle", "controlos": "controles",
    "correcção": "correção", "correcções": "correções",
    "deteção": "detecção", "deteções": "detecções",
    "dialéctica": "dialética", "dialécticas": "dialéticas",
    "dialéctico": "dialético", "dialécticos": "dialéticos",
    "dialecticamente": "dialeticamente",
    "didactica": "didática", "didacticas": "didáticas",
    "didactico": "didático", "didacticos": "didáticos",
    "didáctica": "didática", "didácticas": "didáticas",
    "didáctico": "didático", "didácticos": "didáticos",
    "direcção": "direção", "direcções": "direções",
    "ecrã": "tela", "ecrãs": "telas",
    "económica": "econômica", "económicas": "econômicas",
    "económico": "econômico", "económicos": "econômicos",
    "eletrónica": "eletrônica", "eletrónicas": "eletrônicas",
    "eletrónico": "eletrônico", "eletrónicos": "eletrônicos",
    "equipa": "equipe", "equipas": "equipes",
    "exacta": "exata", "exactas": "exatas",
    "exacto": "exato", "exactos": "exatos",
    "factor": "fator", "factores": "fatores",
    "factorial": "fatorial", "factoriais": "fatoriais",
    "espetro": "espectro", "espetros": "espectros",
    "facto": "fato", "factos": "fatos",
    "fenómeno": "fenômeno", "fenómenos": "fenômenos",
    "ficheiro": "arquivo", "ficheiros": "arquivos",
    "fracção": "fração", "fracções": "frações",
    "género": "gênero", "géneros": "gêneros",
    "heterogénea": "heterogênea", "heterogéneas": "heterogêneas",
    "heterogéneo": "heterogêneo", "heterogéneos": "heterogêneos",
    "homogénea": "homogênea", "homogéneas": "homogêneas",
    "homogéneo": "homogêneo", "homogéneos": "homogêneos",
    "interacção": "interação", "interacções": "interações",
    "metadidactica": "metadidática", "metadidacticas": "metadidáticas",
    "metadidactico": "metadidático", "metadidacticos": "metadidáticos",
    "metadidáctica": "metadidática", "metadidácticas": "metadidáticas",
    "metadidáctico": "metadidático", "metadidácticos": "metadidáticos",
    "objectiva": "objetiva", "objectivas": "objetivas",
    "objectivamente": "objetivamente",
    "objectivo": "objetivo", "objectivos": "objetivos",
    "objecto": "objeto", "objectos": "objetos",
    "perceção": "percepção", "perceções": "percepções",
    "perspetiva": "perspectiva", "perspetivas": "perspectivas",
    "planeamento": "planejamento", "planeamentos": "planejamentos",
    "planear": "planejar",
    "polinómio": "polinômio", "polinómios": "polinômios",
    "projecto": "projeto", "projectos": "projetos",
    "protecção": "proteção", "protecções": "proteções",
    "reacção": "reação", "reacções": "reações",
    "receção": "recepção", "receções": "recepções",
    "registo": "registro", "registos": "registros",
    "respetiva": "respectiva", "respetivas": "respectivas",
    "respetivo": "respectivo", "respetivos": "respectivos",
    "secção": "seção", "secções": "seções",
    "sector": "setor", "sectores": "setores",
    "selecção": "seleção", "selecções": "seleções",
    "sinónimo": "sinônimo", "sinónimos": "sinônimos",
    "sistémica": "sistêmica", "sistémicas": "sistêmicas",
    "sistémico": "sistêmico", "sistémicos": "sistêmicos",
    "milénio": "milênio", "milénios": "milênios",
    "óptima": "ótima", "óptimas": "ótimas",
    "óptimo": "ótimo", "óptimos": "ótimos",
    "utilizadora": "usuária", "utilizadoras": "usuárias",
    "utilizador": "usuário", "utilizadores": "usuários",
    "vector": "vetor", "vectores": "vetores",
}
_PT_BR_WORD_PATTERN = re.compile(
    r"\b(?:" + "|".join(sorted(map(re.escape, _PT_BR_WORDS), key=len, reverse=True)) + r")\b",
    flags=re.IGNORECASE,
)
_PT_BR_PROTECTED_PATTERN = re.compile(
    r"(https?://\S+|www\.\S+|(?:doi\s*:\s*)?10\.\d{4,9}/\S+|"
    r"\b\S+@\S+\.\S+\b|`[^`]*`|\$[^$]*\$|\\\([^)]*\\\)|\\\[[^]]*\\\])",
    flags=re.IGNORECASE,
)
_PT_PT_PROGRESSIVE_PATTERN = re.compile(
    r"\b(estou|estás|está|estamos|estais|estão|estava|estavas|estávamos|"
    r"estáveis|estavam|estive|estiveste|esteve|estivemos|estiveram|estarei|estará|"
    r"estaremos|estarão|estaria|estaríamos|estariam|esteja|estejamos|estejam|"
    r"estivesse|estivéssemos|estivessem)\s+a\s+([A-Za-zÀ-ÖØ-öø-ÿ]+(?:ar|er|ir)|pôr)\b",
    flags=re.IGNORECASE,
)


def _copy_word_case(source, replacement):
    if source.isupper():
        return replacement.upper()
    if source[:1].isupper() and source[1:].islower():
        return replacement[:1].upper() + replacement[1:]
    return replacement


def _portuguese_gerund(infinitive):
    lower = infinitive.lower()
    irregular = {
        "pôr": "pondo", "ser": "sendo", "ter": "tendo", "vir": "vindo",
        "ver": "vendo", "ler": "lendo", "ir": "indo", "haver": "havendo",
        "fazer": "fazendo", "dizer": "dizendo", "trazer": "trazendo",
    }
    if lower in irregular:
        result = irregular[lower]
    elif lower.endswith("ar"):
        result = lower[:-2] + "ando"
    elif lower.endswith("er"):
        result = lower[:-2] + "endo"
    elif lower.endswith("ir"):
        result = lower[:-2] + "indo"
    else:
        return infinitive
    return _copy_word_case(infinitive, result)


def normalizar_portugues_brasileiro(text):
    """Adapta marcas claras de pt-PT sem reescrever o conteúdo traduzido."""
    def adapt_segment(segment):
        segment = _PT_BR_WORD_PATTERN.sub(
            lambda match: _copy_word_case(
                match.group(0), _PT_BR_WORDS[match.group(0).lower()]
            ),
            segment,
        )
        segment = _PT_PT_PROGRESSIVE_PATTERN.sub(
            lambda match: f"{match.group(1)} {_portuguese_gerund(match.group(2))}",
            segment,
        )
        segment = re.sub(r"\bprecisa\s+mente\b", "precisamente", segment, flags=re.IGNORECASE)
        segment = re.sub(r"\bhipó[ -]?sistemas?\b",
                         lambda m: "Hipossistemas" if m.group(0)[:1].isupper() else "hipossistemas",
                         segment, flags=re.IGNORECASE)
        segment = re.sub(r"\b([A-Za-zÀ-ÖØ-öø-ÿ]+)mos-nos\b",
                         lambda m: m.group(1) + "mo-nos", segment, flags=re.IGNORECASE)
        segment = re.sub(r"\baté aos\b", "até os", segment, flags=re.IGNORECASE)
        segment = re.sub(r"\baté ao\b", "até o", segment, flags=re.IGNORECASE)
        segment = re.sub(r"\baté às\b", "até as", segment, flags=re.IGNORECASE)
        segment = re.sub(r"\baté à\b", "até a", segment, flags=re.IGNORECASE)
        segment = re.sub(r"\bmodela-la\b", "modelá-la", segment, flags=re.IGNORECASE)
        segment = re.sub(
            r"\bfração mais pequena\b",
            lambda match: _copy_word_case(match.group(0), "menor fração"),
            segment,
            flags=re.IGNORECASE,
        )
        segment = re.sub(r"\bbem sucedid([oa]s?)\b", r"bem-sucedid\1",
                         segment, flags=re.IGNORECASE)
        segment = re.sub(r"\s+([,.;:!?])", r"\1", segment)
        segment = re.sub(r"([.!?;:])(?=[A-ZÀ-ÖØ-Þ])", r"\1 ", segment)
        return segment

    pieces = _PT_BR_PROTECTED_PATTERN.split(str(text))
    return "".join(piece if index % 2 else adapt_segment(piece)
                   for index, piece in enumerate(pieces))


def _normalizar_variante_portugues(value, target):
    if str(target).strip().lower() != "pt":
        return None
    if value is None or value is False:
        return None
    normalized = str(value).strip().lower().replace("_", "-")
    if normalized in {"", "nenhuma", "nenhum", "desativado", "off", "generic", "genérico", "pt"}:
        return None
    if normalized in {"pt-br", "br", "brasil", "brasileiro", "português-brasileiro"}:
        return "pt-BR"
    raise ValueError("variante_portugues deve ser 'pt-BR' ou None.")


_DIDACTICS_GLOSSARY_FR = (
    (r"\bdidactique des mathématiques\b",
     (r"\bo ensino (?:de|da) matemática\b",), "a didática da matemática"),
    (r"\bdidactique des mathématiques\b",
     (r"\bensino (?:de|da) matemática\b", r"\bdidática (?:de|das) matemáticas?\b",
      r"\bdidática matemática\b"), "didática da matemática"),
    (r"\bsituations didactiques de recherche de problèmes\b",
     (r"\bsituações (?:pedagógicas|didáticas) de (?:pesquisa|investigação) de problemas\b",),
     "situações didáticas de pesquisa de problemas"),
    (r"\bsituation didactique de recherche de problèmes\b",
     (r"\bsituação (?:pedagógica|didática) de (?:pesquisa|investigação) de problemas\b",),
     "situação didática de pesquisa de problemas"),
    (r"\bsituations didactiques\b",
     (r"\bsituações pedagógicas\b",), "situações didáticas"),
    (r"\bsituation didactique\b",
     (r"\bsituação pedagógica\b",), "situação didática"),
    (r"\bactivités didactiques\b",
     (r"\batividades (?:pedagógicas|didáticas)\b",), "atividades didáticas"),
    (r"\bactivité didactique\b",
     (r"\batividade (?:pedagógica|didática)\b",), "atividade didática"),
    (r"\bactivités d[\u2019']enseignement\b",
     (r"\batividades (?:docentes|pedagógicas|de ensino)\b",), "atividades de ensino"),
    (r"\bactivité d[\u2019']enseignement\b",
     (r"\batividade (?:docente|pedagógica|de ensino)\b",), "atividade de ensino"),
    (r"\beffet [«\" ]*jourdain\b",
     (r"\befeit[oa] (?:Jordan|Jordão|Jourdain)\b",), "efeito Jourdain"),
    (r"\bglissement métadidactique\b",
     (r"\b(?:desvio|deslize|deslizamento) metadidático\b",), "deslizamento metadidático"),
    (r"\bsituations a-?didactiques\b",
     (r"\bsituações a-?didáticas\b", r"\bsituações adidáticas\b"), "situações adidáticas"),
    (r"\bsituation a-?didactique\b",
     (r"\bsituação a-?didática\b", r"\bsituação adidática\b"), "situação adidática"),
    (r"\bsituation fondamentale\b",
     (r"\bsituação (?:básica|fundamental)\b",), "situação fundamental"),
    (r"\bsituations fondamentales\b",
     (r"\bsituações (?:básicas|fundamentais)\b",), "situações fundamentais"),
    (r"\btransposition didactique\b",
     (r"\btransposição didática\b",), "transposição didática"),
    (r"\bcontrat didactique\b",
     (r"\bcontrato (?:de ensino|docente|didático)\b",), "contrato didático"),
    (r"\bsavoir savant\b",
     (r"\b(?:conhecimento|saber) (?:erudito|científico|sábio)\b",), "saber sábio"),
    (r"\bsavoirs? et (?:les )?connaissances?\b",
     (r"\b(?:os )?conhecimentos e (?:os )?conhecimentos\b",),
     "os saberes e os conhecimentos"),
    (r"\bconnaissances? et (?:les )?savoirs?\b",
     (r"\b(?:os )?conhecimentos e (?:os )?conhecimentos\b",),
     "os conhecimentos e os saberes"),
    (r"\bénoncés\b",
     (r"\bas (?:afirmações|declarações)\b",), "os enunciados"),
    (r"\bénoncés\b",
     (r"\bafirmações\b", r"\bdeclarações\b"), "enunciados"),
    (r"\bénoncé\b",
     (r"\ba (?:afirmação|declaração)\b",), "o enunciado"),
    (r"\bénoncé\b",
     (r"\bafirmação\b", r"\bdeclaração\b"), "enunciado"),
    (r"\bdécroissance\b",
     (r"\ba (?:descreção|descrição|diminuição)\b",), "o decrescimento"),
    (r"\bdécroissance\b",
     (r"\b(?:descreção|descrição|diminuição)\b",), "decrescimento"),
    (r"\bmathématisation verticale\b",
     (r"\b(?:matemática|matematização) vertical\b",), "matematização vertical"),
    (r"\brétroactions\b",
     (r"\bfeedbacks?\b",), "retroações"),
    (r"\brétroaction\b",
     (r"\bfeedback\b",), "retroação"),
    (r"\bmilieux\b",
     (r"\bos ambientes\b",), "os meios"),
    (r"\bmilieux\b",
     (r"\bambientes\b",), "meios"),
    (r"\bmilieu\b",
     (r"\bo ambiente\b",), "o meio"),
    (r"\bmilieu\b",
     (r"\bambiente\b",), "meio"),
    (r"\bmaître\b",
     (r"\b(?:capitão|mestre)\b",), "professor"),
    (r"\bjeux principaux du maître\b",
     (r"\b(?:desafios|jogos) (?:principais )?do capitão\b",),
     "jogos principais do professor"),
    (r"\brecherche de problèmes\b",
     (r"\binvestigação de problemas\b",), "pesquisa de problemas"),
    (r"\bpreuves\b",
     (r"\bevidências\b",), "provas"),
    (r"\bpreuve\b",
     (r"\bevidência\b",), "prova"),
    (r"\bhyposystèmes?\b",
     (r"\bhipó[ -]?sistemas?\b", r"\bhipossistemas?\b"), "hipossistemas"),
    (r"\bde plus en plus nombreux\b",
     (r"\bcada vez mais breves\b", r"\bcada vez mais numerosos\b"), "cada vez mais numerosos"),
)

_DIDACTICS_GLOSSARY_IT = (
    (r"\bsituazioni didattiche\b",
     (r"\bsituações pedagógicas\b",), "situações didáticas"),
    (r"\bsituazione didattica\b",
     (r"\bsituação pedagógica\b",), "situação didática"),
)

_DIDACTICS_GLOSSARY_EN = (
    (r"\bdidactical situations\b",
     (r"\bsituações pedagógicas\b",), "situações didáticas"),
    (r"\bdidactical situation\b",
     (r"\bsituação pedagógica\b",), "situação didática"),
)


def _normalizar_perfil_terminologico(value):
    if value is None or value is False:
        return None
    normalized = str(value).strip().lower().replace("-", "_").replace(" ", "_")
    if normalized in {"", "nenhum", "none", "off", "geral", "generico", "genérico"}:
        return None
    if normalized in {"didatica", "didatica_matematica", "tsd", "tad_tsd"}:
        return "didatica_matematica"
    raise ValueError("perfil_terminologico deve ser 'didatica_matematica' ou None.")


def _normalizar_glossario_personalizado(value):
    if value is None:
        return {}
    if not isinstance(value, dict):
        raise TypeError("glossario_personalizado deve ser um dicionário.")
    result = {}
    for source, target in value.items():
        source, target = str(source).strip(), str(target).strip()
        if source and target:
            result[source] = target
    return result


def aplicar_glossario_terminologico(source_text, translated_text, source_language,
                                    profile=None, custom_glossary=None):
    """Corrige termos conhecidos sem solicitar outra tradução ao modelo."""
    result, changes = str(translated_text), 0
    if profile == "didatica_matematica":
        tables = {
            "fr": _DIDACTICS_GLOSSARY_FR,
            "it": _DIDACTICS_GLOSSARY_IT,
            "en": _DIDACTICS_GLOSSARY_EN,
        }
        for source_pattern, output_patterns, preferred in tables.get(source_language, ()):
            if not re.search(source_pattern, source_text, flags=re.IGNORECASE):
                continue
            for output_pattern in output_patterns:
                updated, count = re.subn(
                    output_pattern,
                    lambda match: _copy_word_case(match.group(0), preferred),
                    result,
                    count=1,
                    flags=re.IGNORECASE,
                )
                if count:
                    result, changes = updated, changes + count
                    break
    for found, preferred in (custom_glossary or {}).items():
        pattern = r"(?<!\w)" + re.escape(found) + r"(?!\w)"
        result, count = re.subn(
            pattern,
            lambda match: _copy_word_case(match.group(0), preferred),
            result,
            flags=re.IGNORECASE,
        )
        changes += count
    return result, changes


# Elementos que não devem ser recriados pelo modelo. A proteção ocorre antes
# da tradução e a restauração exige que cada marcador volte exatamente uma vez.
_TECHNICAL_MATH_ATOM = (
    r"(?:[A-Za-zΑ-Ωα-ω](?:\d+|[₀-₉⁰¹²³⁴⁵⁶⁷⁸⁹]+)?|"
    r"[A-Za-zΑ-Ωα-ω]\s*\([^()\n]{1,60}\)|"
    r"\([^()\n]{1,60}\)|"
    r"\d+(?:[.,]\d+)?(?:[eE][+-]?\d+)?"
    r"(?:[A-Za-zΑ-Ωα-ω](?:\d+|[₀-₉⁰¹²³⁴⁵⁶⁷⁸⁹]+)?)?)"
)
_TECHNICAL_PROTECTION_PATTERNS = (
    ("url", re.compile(r"https?://[^\s<>()]+|www\.[^\s<>()]+", re.IGNORECASE)),
    ("email", re.compile(r"\b[^\s@]+@[^\s@]+\.[^\s@]+\b")),
    ("doi", re.compile(r"(?:doi\s*:\s*)?10\.\d{4,9}/[^\s<>()]+", re.IGNORECASE)),
    ("latex", re.compile(r"\$[^$\n]+\$|\\\([^\n]*?\\\)|\\\[[^\n]*?\\\]")),
    ("citacao", re.compile(
        r"\([^()\n]{0,220}\b(?:18|19|20)\d{2}[a-z]?\b[^()\n]{0,220}\)"
    )),
    ("conjunto", re.compile(r"\{[^{}\n]{1,160}\}")),
    ("formula", re.compile(
        rf"(?<!\w){_TECHNICAL_MATH_ATOM}"
        rf"(?:\s*(?:=|≠|≤|≥|<|>|→|↦|≈|∼|±|∓|∈|∉|⊂|⊆|\+|−|×|÷|/|\^)\s*"
        rf"{_TECHNICAL_MATH_ATOM}){{1,}}(?!\w)"
    )),
    ("intervalo", re.compile(r"(?<!\w)\d+\s*[–—-]\s*\d+(?!\w)")),
    ("rotulo", re.compile(r"\b[A-Z]\d+\b")),
    ("sigla", re.compile(r"\b[A-Z][A-Z0-9]{1,9}\b")),
)


class ProtectedElementError(RuntimeError):
    pass


def proteger_elementos_tecnicos(text):
    """Substitui fórmulas, citações e identificadores por marcadores estáveis."""
    original = str(text)
    candidates = []
    for priority, (kind, pattern) in enumerate(_TECHNICAL_PROTECTION_PATTERNS):
        for match in pattern.finditer(original):
            candidates.append((match.start(), match.end(), priority, kind, match.group(0)))
    candidates.sort(key=lambda item: (item[0], -(item[1] - item[0]), item[2]))

    selected, last_end = [], -1
    for candidate in candidates:
        start, end = candidate[:2]
        if start < last_end:
            continue
        selected.append(candidate)
        last_end = end

    if not selected:
        return original, [], [(False, original)]

    masked, elements, segments, cursor = [], [], [], 0
    for index, (start, end, _, kind, value) in enumerate(selected):
        if start > cursor:
            plain = original[cursor:start]
            masked.append(plain)
            segments.append((False, plain))
        marker = f"ZXQKEEP{index:04d}QXZ"
        masked.append(marker)
        segments.append((True, value))
        elements.append({"marker": marker, "original": value, "tipo": kind})
        cursor = end
    if cursor < len(original):
        plain = original[cursor:]
        masked.append(plain)
        segments.append((False, plain))
    return "".join(masked), elements, segments


def restaurar_elementos_tecnicos(text, elements):
    """Restaura os marcadores e falha se o modelo apagar ou duplicar algum."""
    result = str(text)
    for item in elements:
        marker, original = item["marker"], item["original"]
        result, count = re.subn(re.escape(marker), lambda _: original, result)
        if count == 0:
            # Alguns tokenizadores inserem espaços dentro de sequências raras.
            tolerant = r"\s*".join(re.escape(char) for char in marker)
            result, count = re.subn(tolerant, lambda _: original, result,
                                    count=1, flags=re.IGNORECASE)
        if count != 1:
            raise ProtectedElementError(
                f"O marcador técnico {marker} foi alterado pelo modelo."
            )
    if re.search(r"ZXQ\s*KEEP", result, flags=re.IGNORECASE):
        raise ProtectedElementError("Restou um marcador técnico na tradução.")
    return normalize_spaces(result)


def elementos_tecnicos(text):
    """Retorna apenas os elementos protegíveis, para auditoria e testes."""
    _, elements, _ = proteger_elementos_tecnicos(text)
    return [item["original"] for item in elements]


def join_lines(lines):
    """Reconstrói texto corrido sem manter hifens de quebra de linha."""
    out = ""
    for raw in lines:
        s = normalize_spaces(raw)
        if not s:
            continue

        if not out:
            out = s
            continue

        # Preserva itens de lista como nova linha.
        if re.match(r"^[•●▪◦‣*-]\s+", s):
            out += "\n" + s
            continue

        # Palavra quebrada no fim da linha: "trans-" + "lation".
        if out.endswith("-") and s[:1].islower():
            out = out[:-1] + s
        else:
            out += " " + s

    return normalize_spaces(out)


def margin_key(text: str) -> str:
    """Normaliza cabeçalhos/rodapés para reconhecer repetições entre páginas."""
    t = normalize_spaces(text).lower()
    t = re.sub(r"\b\d+\b", "#", t)
    t = re.sub(r"\s+", " ", t)
    return t.strip(" |–—-.,;:")


def is_machine_noise(text: str) -> bool:
    """Ignora elementos que não vale a pena mandar ao tradutor."""
    t = normalize_spaces(text)
    if not t:
        return True

    if len(re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ]", t)) < MIN_ALPHA_CHARS:
        return True

    # Página / paginação isolada: "3", "3/12", "Page 3 of 12" etc.
    if re.fullmatch(r"\s*(?:page\s*)?\d+(?:\s*(?:/|of)\s*\d+)?\s*", t, re.I):
        return True

    # URL / DOI / ORCID / e-mail isolados ou quase isolados.
    if re.fullmatch(r"(?:https?://|www\.)\S+", t, re.I):
        return True
    if re.fullmatch(r"(?:doi\s*:\s*)?10\.\d{4,9}/\S+", t, re.I):
        return True
    if "orcid.org/" in t.lower() and len(t.split()) <= 3:
        return True
    if re.fullmatch(r"\S+@\S+\.\S+", t):
        return True

    return False


def is_probable_heading(text: str, font_size: float, body_size: float) -> bool:
    t = normalize_spaces(text)
    if not t or len(t) > 180:
        return False

    letters = [c for c in t if c.isalpha()]
    upper_ratio = (sum(c.isupper() for c in letters) / len(letters)) if letters else 0

    if font_size > body_size * 1.15:
        return True
    if len(t.split()) <= 12 and upper_ratio > 0.72:
        return True
    return False


# ============================================================
# EXTRAÇÃO E ORDEM DE LEITURA
# ============================================================
def line_text(line: dict) -> str:
    return normalize_spaces("".join(span.get("text", "") for span in line.get("spans", [])))


def line_font_size(line: dict) -> float:
    sizes = [float(span.get("size", 0)) for span in line.get("spans", []) if span.get("text", "").strip()]
    return statistics.median(sizes) if sizes else 0.0


def collect_repeated_margin_keys(doc) -> set:
    """Descobre cabeçalhos/rodapés repetidos para não traduzi-los página a página."""
    counts = {}
    pages_seen = {}

    for page_no, page in enumerate(doc):
        h = page.rect.height
        data = page.get_text("dict", sort=False)

        for block in data.get("blocks", []):
            if block.get("type") != 0:
                continue
            for line in block.get("lines", []):
                text = line_text(line)
                if not text:
                    continue
                x0, y0, x1, y1 = line.get("bbox", (0, 0, 0, 0))
                in_margin = y1 <= h * HEADER_FOOTER_ZONE or y0 >= h * (1 - HEADER_FOOTER_ZONE)
                if not in_margin:
                    continue

                key = margin_key(text)
                if len(key) < 3:
                    continue
                pages_seen.setdefault(key, set()).add(page_no)

    for key, page_set in pages_seen.items():
        counts[key] = len(page_set)

    threshold = max(
        REPEATED_MARGIN_MIN_PAGES,
        int(len(doc) * REPEATED_MARGIN_MIN_RATIO + 0.999),
    )
    return {key for key, n in counts.items() if n >= threshold}


def extract_blocks(page, repeated_margin_keys):
    """Extrai parágrafos com quads precisos, mesmo dentro do mesmo bloco PDF."""
    data = page.get_text("dict", sort=False)
    h = page.rect.height
    result = []

    for block in data.get("blocks", []):
        if block.get("type") != 0:
            continue

        line_items = []

        for line in block.get("lines", []):
            text = line_text(line)
            if not text:
                continue

            bbox = fitz.Rect(line.get("bbox", (0, 0, 0, 0)))
            in_margin = bbox.y1 <= h * HEADER_FOOTER_ZONE or bbox.y0 >= h * (1 - HEADER_FOOTER_ZONE)
            if in_margin and margin_key(text) in repeated_margin_keys:
                continue
            if in_margin and re.fullmatch(r"\s*\d+(?:\s*/\s*\d+)?\s*", text):
                continue
            if is_machine_noise(text):
                continue

            try:
                quad = fitz.recover_line_quad(line)
            except Exception:
                quad = fitz.Quad(bbox)
            line_items.append({"text": text, "rect": bbox, "quad": quad,
                               "font_size": line_font_size(line)})

        if not line_items:
            continue

        sizes = [item["font_size"] for item in line_items if item["font_size"] > 0]
        typical_size = statistics.median(sizes) if sizes else 10.0
        base_x = min(item["rect"].x0 for item in line_items)
        groups = []
        for item in line_items:
            begins = item["text"].lstrip(' «“\"\'([{')[:1]
            starts_normally = bool(begins and (begins.isupper() or begins.isdigit()))
            if groups:
                previous = groups[-1][-1]
                gap = item["rect"].y0 - previous["rect"].y1
                indented = item["rect"].x0 - base_x >= max(5.0, typical_size * 0.75)
                extra_gap = gap >= max(1.5, typical_size * 0.14)
                previous_complete = bool(re.search(r'[.!?][0-9”"»’)]*\s*$', previous["text"]))
                if previous_complete and starts_normally and (indented or extra_gap):
                    groups.append([])
            if not groups:
                groups.append([])
            groups[-1].append(item)

        for group_index, group in enumerate(groups):
            text = join_lines([item["text"] for item in group])
            if is_machine_noise(text):
                continue
            rect = fitz.Rect(group[0]["rect"])
            for item in group[1:]:
                rect.include_rect(item["rect"])
            group_sizes = [item["font_size"] for item in group if item["font_size"] > 0]
            result.append({
                "text": text,
                "rect": rect,
                "quads": [item["quad"] for item in group],
                "font_size": statistics.median(group_sizes) if group_sizes else 0.0,
                "line_items": group,
                # Impede que a etapa seguinte reúna novamente parágrafos
                # que estavam dentro do mesmo bloco interno do PDF.
                "paragraph_break_before": group_index > 0,
            })

    return result


def detect_two_columns(blocks, page_width: float) -> bool:
    """Reconhece colunas sustentadas, não apenas elementos laterais isolados.

    PDFs antigos frequentemente guardam autores, títulos ou legendas como
    vários blocos curtos à direita. Contar apenas blocos fazia esses elementos
    transformarem falsamente uma página de uma coluna em duas colunas, deixando
    cada linha do corpo como uma unidade de tradução independente.
    """
    candidates = [b for b in blocks if b["rect"].width < page_width * 0.62]
    left, right = [], []
    for block in candidates:
        rect = block["rect"]
        center = (rect.x0 + rect.x1) / 2
        if center <= page_width * 0.46 and rect.x1 <= page_width * 0.64:
            left.append(block)
        elif center >= page_width * 0.54 and rect.x0 >= page_width * 0.36:
            right.append(block)

    if len(left) < 3 or len(right) < 3:
        return False
    if sum(len(b["text"]) for b in left) < 120 or sum(len(b["text"]) for b in right) < 120:
        return False

    left_top, left_bottom = min(b["rect"].y0 for b in left), max(b["rect"].y1 for b in left)
    right_top, right_bottom = min(b["rect"].y0 for b in right), max(b["rect"].y1 for b in right)
    overlap = max(0.0, min(left_bottom, right_bottom) - max(left_top, right_top))
    smaller_span = min(left_bottom - left_top, right_bottom - right_top)
    if smaller_span <= 0 or overlap / smaller_span < 0.45:
        return False

    # Em colunas reais há vários blocos ocupando faixas verticais próximas.
    # Uma assinatura/autoria lateral costuma formar apenas um pequeno grupo.
    smaller, larger = (left, right) if len(left) <= len(right) else (right, left)
    matches = 0
    for block in smaller:
        rect = block["rect"]
        center = (rect.y0 + rect.y1) / 2
        tolerance = max(24.0, float(block.get("font_size", 0)) * 2.5)
        if any(other["rect"].y0 - tolerance <= center <= other["rect"].y1 + tolerance
               for other in larger):
            matches += 1
    return matches >= 3


def block_column(block, page_width: float, two_columns: bool):
    r = block["rect"]
    if not two_columns:
        return "single"
    if r.width >= page_width * 0.72 or (r.x0 < page_width * 0.28 and r.x1 > page_width * 0.72):
        return "wide"
    return "left" if r.x0 + r.x1 < page_width else "right"


def order_blocks(blocks, page_width: float):
    """Evita o erro clássico y/x que intercala as duas colunas linha a linha."""
    if not blocks:
        return []

    two_columns = detect_two_columns(blocks, page_width)
    for b in blocks:
        b["column"] = block_column(b, page_width, two_columns)

    if not two_columns:
        return sorted(blocks, key=lambda b: (b["rect"].y0, b["rect"].x0))

    wide = sorted([b for b in blocks if b["column"] == "wide"], key=lambda b: b["rect"].y0)
    narrow = [b for b in blocks if b["column"] != "wide"]

    ordered = []
    band_top = -1e9

    # Blocos largos funcionam como separadores de faixas: título, abstract, heading etc.
    for wb in wide:
        band_bottom = wb["rect"].y0
        band = [b for b in narrow if band_top <= b["rect"].y0 < band_bottom]
        ordered.extend(sorted([b for b in band if b["column"] == "left"], key=lambda b: b["rect"].y0))
        ordered.extend(sorted([b for b in band if b["column"] == "right"], key=lambda b: b["rect"].y0))
        ordered.append(wb)
        band_top = wb["rect"].y1

    band = [b for b in narrow if b["rect"].y0 >= band_top]
    ordered.extend(sorted([b for b in band if b["column"] == "left"], key=lambda b: b["rect"].y0))
    ordered.extend(sorted([b for b in band if b["column"] == "right"], key=lambda b: b["rect"].y0))

    # Segurança: não perder bloco por casos geométricos estranhos.
    seen = {id(b) for b in ordered}
    ordered.extend(b for b in blocks if id(b) not in seen)
    return ordered


def body_font_size(blocks):
    vals = [b["font_size"] for b in blocks if b["font_size"] > 0 and len(b["text"]) > 80]
    return statistics.median(vals) if vals else 10.0


def should_merge(prev, cur, body_size: float) -> bool:
    if cur.get("paragraph_break_before"):
        return False
    if prev["column"] != cur["column"]:
        return False
    pr, cr = prev["rect"], cur["rect"]
    gap = cr.y0 - pr.y1
    fs = max(prev["font_size"], cur["font_size"], body_size, 1.0)

    if gap < -fs * 0.4 or gap > fs * 1.05:
        return False

    overlap = max(0.0, min(pr.x1, cr.x1) - max(pr.x0, cr.x0))
    overlap_ratio = overlap / max(1.0, min(pr.width, cr.width))
    aligned = overlap_ratio >= 0.55 or abs(pr.x0 - cr.x0) <= fs * 1.2
    if not aligned:
        return False

    if prev["font_size"] and cur["font_size"]:
        ratio = max(prev["font_size"], cur["font_size"]) / max(0.1, min(prev["font_size"], cur["font_size"]))
        if ratio > 1.25:
            return False

    prev_heading = is_probable_heading(prev["text"], prev["font_size"], body_size)
    cur_heading = is_probable_heading(cur["text"], cur["font_size"], body_size)
    if prev_heading and cur_heading:
        centers_close = abs((pr.x0 + pr.x1) / 2 - (cr.x0 + cr.x1) / 2) <= fs * 3.0
        return (centers_close and gap <= fs * 1.8 and
                not re.search(r"[.!?;:]\s*$", prev["text"]))

    if prev["column"] == "wide":
        return False
    if is_probable_heading(cur["text"], cur["font_size"], body_size):
        return False

    # Se o bloco anterior termina no meio de palavra/frase, é forte candidato a continuação.
    if prev["text"].endswith("-"):
        return True
    if not re.search(r"[.!?;:]\s*$", prev["text"]):
        return True

    # Mesmo com pontuação, PDFs às vezes quebram o mesmo parágrafo em blocos muito próximos.
    return gap <= fs * 0.35 and abs(pr.x0 - cr.x0) <= fs * 0.7


def merge_text(a: str, b: str) -> str:
    if a.endswith("-") and b[:1].islower():
        return a[:-1] + b
    return a + " " + b


def _unit_from_lines(template, lines):
    rect = fitz.Rect(lines[0]["rect"])
    for line in lines[1:]:
        rect.include_rect(line["rect"])
    sizes = [line["font_size"] for line in lines if line["font_size"] > 0]
    item = dict(template)
    item.update(text=join_lines([line["text"] for line in lines]), rect=rect,
                quads=[line["quad"] for line in lines], line_items=list(lines),
                font_size=statistics.median(sizes) if sizes else template["font_size"])
    return item


def _split_large_unit(unit, max_chars):
    if len(unit["text"]) <= max_chars or not unit.get("line_items"):
        return [unit]
    # ``max_chars`` é um alvo, não uma guilhotina. O NLLB já recebe as
    # sentenças separadamente; aqui só dividimos quando existe uma fronteira
    # segura. Isso evita comentários terminados em "a", "de", "que" etc.
    lines, pieces, start = unit["line_items"], [], 0
    hard_limit = max(MAX_CHARS_PER_REQUEST, int(max_chars * 1.6))
    while start < len(lines):
        sizes, total = {}, 0
        for end in range(start + 1, len(lines) + 1):
            total += len(lines[end - 1]["text"]) + (1 if end - 1 > start else 0)
            sizes[end] = total

        if total <= max_chars:
            end = len(lines)
        else:
            safe = [end for end, size in sizes.items()
                    if max_chars * 0.55 <= size <= max_chars * 1.35 and
                    re.search(r'[.!?;:][0-9”"»’)]*\s*$', lines[end - 1]["text"])]
            if safe:
                end = min(safe, key=lambda point: abs(sizes[point] - max_chars))
            elif total <= hard_limit:
                end = len(lines)
            else:
                within_hard = [end for end, size in sizes.items() if size <= hard_limit]
                end = within_hard[-1] if within_hard else start + 1
        pieces.append(_unit_from_lines(unit, lines[start:end]))
        start = end
    return pieces


def make_logical_units(ordered_blocks, max_chars=MAX_CHARS_PER_UNIT, merge_blocks=True):
    if not ordered_blocks:
        return []

    bsize = body_font_size(ordered_blocks)
    units = []

    for block in ordered_blocks:
        item = {
            "text": block["text"],
            "rect": fitz.Rect(block["rect"]),
            "quads": list(block["quads"]),
            "font_size": block["font_size"],
            "column": block["column"],
            "line_items": list(block.get("line_items", [])),
            "paragraph_break_before": block.get("paragraph_break_before", False),
        }

        if merge_blocks and units and should_merge(units[-1], item, bsize):
            prev = units[-1]
            prev["text"] = merge_text(prev["text"], item["text"])
            prev["rect"].include_rect(item["rect"])
            prev["quads"].extend(item["quads"])
            prev["line_items"].extend(item["line_items"])
            prev["font_size"] = statistics.median([prev["font_size"], item["font_size"]])
        else:
            units.append(item)

    limited = []
    for unit in units:
        limited.extend(_split_large_unit(unit, max(200, int(max_chars))))
    return limited


_REFERENCE_HEADING_PATTERN = re.compile(
    r"^(?:\d+(?:\.\d+)*[.)]?\s*)?"
    r"(?:bibliograph(?:ie|y)|bibliografia|"
    r"références?(?:\s+bibliographiques?)?|references?|"
    r"referências?(?:\s+bibliográficas?)?|works cited|obras citadas)\s*[:.]?\s*$",
    flags=re.IGNORECASE,
)
_POST_REFERENCE_HEADING_PATTERN = re.compile(
    r"^(?:annexes?|appendices?|apêndices?|supplementary material|material suplementar)\b",
    flags=re.IGNORECASE,
)


def _unit_first_line(unit):
    lines = unit.get("line_items") or []
    return normalize_spaces(lines[0]["text"] if lines else unit.get("text", "").split("\n", 1)[0])


def is_reference_heading(unit):
    """Reconhece o título da seção, mesmo quando a primeira referência foi anexada."""
    first = _unit_first_line(unit)
    if _REFERENCE_HEADING_PATTERN.fullmatch(first):
        return True
    text = normalize_spaces(unit.get("text", ""))
    match = re.match(
        r"^(?:\d+(?:\.\d+)*[.)]?\s*)?"
        r"(?:bibliograph(?:ie|y)|bibliografia|références?|references?|"
        r"referências?|works cited|obras citadas)\b",
        text,
        flags=re.IGNORECASE,
    )
    return bool(match and len(match.group(0).split()) <= 3)


def marcar_secao_referencias(units_by_page):
    """Marca a bibliografia para preservação, sem alterar o texto original."""
    active, start = False, None
    for page_number in sorted(units_by_page):
        for index, unit in enumerate(units_by_page[page_number]):
            first = _unit_first_line(unit)
            if active and _POST_REFERENCE_HEADING_PATTERN.match(first):
                active = False
            if is_reference_heading(unit):
                active = True
                start = start or {"pagina": page_number, "trecho": index + 1}
            if active:
                unit["preservar_referencia"] = True
    return start


def _is_caption_or_footnote(unit, body_size):
    text = normalize_spaces(unit.get("text", ""))
    if re.match(r"^(?:fig(?:ure|ura)?\.?|tableau|tabela|quadro)\s*\d*\b", text, re.I):
        return True
    if unit.get("font_size", body_size) < body_size * 0.82:
        return True
    if re.match(r"^\d+\s+", text) and unit.get("font_size", body_size) < body_size * 0.95:
        return True
    return False


def _source_looks_unfinished(text):
    value = normalize_spaces(text).rstrip()
    if len(value) < 35:
        return False
    if value.endswith("-"):
        return True
    if re.search(r'[.!?][”"»’)]*$', value):
        return False
    last = re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ]+", value.lower())
    return (not re.search(r'[.;!?][”"»’)]*$', value) or
            bool(last and last[-1] in {
                "a", "au", "aux", "avec", "de", "des", "du", "et", "la", "le",
                "les", "ou", "par", "pour", "que", "qui", "un", "une",
                "da", "das", "de", "do", "dos", "e", "o", "os", "que",
            }))


def _source_begins_as_continuation(text):
    value = normalize_spaces(text).lstrip(' «“"\'([{—–-')
    return bool(value and (value[:1].islower() or value[:1] in ",;:)]"))


def encontrar_continuacoes_entre_paginas(units_by_page, page_heights):
    """Liga fragmentos corporais que continuam na página seguinte.

    A mesma tradução integral é associada aos dois realces. Isso é deliberado:
    dividir novamente a frase traduzida por proporção poderia deslocar o sentido.
    """
    mapping, groups = {}, []
    numbers = sorted(units_by_page)
    for left_page, right_page in zip(numbers, numbers[1:]):
        if right_page != left_page + 1:
            continue
        left_units, right_units = units_by_page[left_page], units_by_page[right_page]
        if not left_units or not right_units:
            continue
        left_body, right_body = body_font_size(left_units), body_font_size(right_units)
        left_candidates = [
            (index, unit) for index, unit in enumerate(left_units)
            if not unit.get("preservar_referencia")
            and unit["rect"].y1 >= page_heights[left_page] * 0.58
            and not _is_caption_or_footnote(unit, left_body)
            and not is_probable_heading(unit["text"], unit["font_size"], left_body)
        ]
        right_candidates = [
            (index, unit) for index, unit in enumerate(right_units)
            if not unit.get("preservar_referencia")
            and unit["rect"].y0 <= page_heights[right_page] * 0.42
            and not _is_caption_or_footnote(unit, right_body)
            and not is_probable_heading(unit["text"], unit["font_size"], right_body)
        ]
        if not left_candidates or not right_candidates:
            continue
        left_index, left = left_candidates[-1]
        right_index, right = right_candidates[0]
        if not (_source_looks_unfinished(left["text"]) and
                _source_begins_as_continuation(right["text"])):
            continue
        combined = merge_text(left["text"], right["text"])
        if len(combined) > MAX_CHARS_PER_REQUEST:
            continue
        group_id = f"p{left_page}t{left_index + 1}-p{right_page}t{right_index + 1}"
        group = {"id": group_id, "paginas": [left_page, right_page],
                 "texto": combined,
                 "membros": [(left_page, left_index), (right_page, right_index)]}
        groups.append(group)
        for member in group["membros"]:
            mapping[member] = group
    return mapping, groups


_AUDIT_PT_PT = dict(_PT_BR_WORDS)
_AUDIT_END_WORDS = {
    "a", "as", "com", "como", "da", "das", "de", "do", "dos", "e", "em",
    "na", "nas", "no", "nos", "o", "os", "para", "por", "que", "se", "um", "uma",
}


def auditar_traducao(source_text, translated_text, source_language=None):
    """Aponta trechos para revisão sem bloquear nem refazer uma boa tradução."""
    source, target = normalize_spaces(source_text), normalize_spaces(translated_text)
    flags = []

    def add(code, message):
        if not any(item["codigo"] == code for item in flags):
            flags.append({"codigo": code, "mensagem": message})

    source_words = re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ]+", source)
    target_words = re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ]+", target)
    if len(source_words) >= 18:
        ratio = len(target_words) / max(1, len(source_words))
        if ratio < 0.62:
            add("saida_curta", f"Tradução curta em relação ao original ({ratio:.0%}).")
        elif ratio > 1.75:
            add("saida_longa", f"Tradução longa em relação ao original ({ratio:.0%}).")

    final_words = re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ]+", target.lower())
    if len(target_words) >= 8 and final_words and final_words[-1] in _AUDIT_END_WORDS:
        add("final_suspenso", f"A tradução termina em “{final_words[-1]}”.")
    if (len(source_words) >= 12 and re.search(r'[.!?][”"»’)]*$', source) and
            not re.search(r'[.!?][”"»’)]*$', target)):
        add("pontuacao_final", "O original termina a frase, mas a tradução não.")
    source_final_words = re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ]+", source.lower())
    strong_open_end = bool(
        source.endswith(("-", ",", ";", ":"))
        or (source_final_words and source_final_words[-1] in _AUDIT_END_WORDS)
        or (source_final_words and len(source_final_words[-1]) <= 3
            and not re.search(r'[.!?][”"»’)]*$', source))
    )
    if _source_looks_unfinished(source) and strong_open_end:
        add("origem_fragmentada", "O bloco original parece terminar no meio da frase.")

    missing = [atom for atom in elementos_tecnicos(source) if atom not in target]
    if missing:
        add("elemento_tecnico_alterado",
            "Elemento técnico ausente ou alterado: " + ", ".join(missing[:3]))
    if re.search(r"ZXQ\s*KEEP", target, flags=re.IGNORECASE):
        add("marcador_exposto", "Um marcador interno apareceu na tradução.")

    lowered = target.lower()
    residues = sorted({word for word in _AUDIT_PT_PT
                       if re.search(r"\b" + re.escape(word) + r"\b", lowered)})
    if residues:
        add("portugues_europeu", "Forma não brasileira: " + ", ".join(residues))
    if _PT_PT_PROGRESSIVE_PATTERN.search(target):
        add("portugues_europeu", "Construção progressiva de português europeu ainda presente.")

    semantic_checks = (
        (r"\bmaître\b", r"\bcapitão\b", "maître foi traduzido como capitão"),
        (r"\bdécroissance\b", r"\b(?:descreção|descrição)\b", "décroissance exige decrescimento"),
        (r"\beffet\s+jourdain\b", r"\befeit[oa]\s+(?:jordão|jordan)\b", "manter efeito Jourdain"),
        (r"\bmathématisation verticale\b", r"\bmatemática vertical\b", "usar matematização vertical"),
    )
    if source_language == "fr":
        for source_pattern, target_pattern, message in semantic_checks:
            if re.search(source_pattern, source, re.I) and re.search(target_pattern, target, re.I):
                add("termo_suspeito", message)
    return flags


# ============================================================
# TRADUÇÃO COM CACHE E RETENTATIVAS
# ============================================================
class TranslationError(RuntimeError):
    pass


class LocalChunkError(TranslationError):
    """Saída local inválida para um trecho; permite continuar o documento.

    Erros de instalação, CUDA, memória, disco e interrupções não pertencem
    a esta classe: devem salvar o progresso e ser explicitados ao usuário.
    """


def _finite_number(value, name, minimum=0):
    value = float(value)
    if not math.isfinite(value) or value < minimum:
        raise ValueError(f"{name} deve ser um número finito >= {minimum}.")
    return value


def load_cache(path):
    path = Path(path)
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except (ValueError, UnicodeError):
        print(f"Aviso: JSON inválido em {path.name}; entradas não serão reutilizadas.")
        return {}


def save_cache(path, cache):
    """Gravação atômica: a interrupção não deixa o JSON pela metade."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(cache, stream, ensure_ascii=False, indent=2, allow_nan=False)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


def cache_key(text, source_lang, target_lang):
    return hashlib.sha256(f"{source_lang}\0{target_lang}\0{text}".encode("utf-8")).hexdigest()


def is_transient_translation_error(value):
    # Não considera números como 429/503 em um artigo como mensagens de erro.
    if not isinstance(value, str):
        return False
    text = value.strip()
    return bool(re.search(
        r"^(?:<!doctype\s+html|<html\b|<head\b|<body\b|"
        r"(?:error|http)\s*[45]\d\d\b|[45]\d\d\s*\((?:server|client) error\)|"
        r"server error:|too many requests(?:[.!]|$)|"
        r"our systems have detected unusual traffic|todos os motores disponíveis falharam)",
        text, re.I))


def _valid_cached_translation(value):
    return isinstance(value, str) and bool(value.strip()) and not is_transient_translation_error(value)


def sanitize_translation_cache(cache):
    if not isinstance(cache, dict):
        return {}, 0
    valid = {k: v for k, v in cache.items() if _valid_cached_translation(v)}
    return valid, len(cache) - len(valid)


def split_text(text, limit=MAX_CHARS_PER_REQUEST):
    """Limita também o tamanho da URL, inclusive em idiomas com muitos acentos."""
    if not isinstance(limit, int) or limit < 20:
        raise ValueError("O limite por trecho deve ser um inteiro >= 20.")
    remaining = normalize_spaces(text)
    parts = []
    while remaining:
        low, high = 1, min(limit, len(remaining))
        while low < high:
            middle = (low + high + 1) // 2
            if len(urllib.parse.quote_plus(remaining[:middle])) <= 5500:
                low = middle
            else:
                high = middle - 1
        size = low
        if size < len(remaining):
            ends = list(re.finditer(r"[.!?;:]\s+", remaining[:size]))
            boundary = ends[-1].end() if ends else remaining.rfind(" ", 0, size)
            if boundary >= size * 0.5:
                size = boundary
        part = remaining[:size].strip()
        if part:
            parts.append(part)
        remaining = remaining[size:].lstrip()
    return parts


class _FileLock:
    """Trava de processo liberada pelo SO, inclusive se o Jupyter for encerrado."""
    def __init__(self, path, timeout=60):
        self.path, self.timeout, self.file = Path(path), timeout, None

    def __enter__(self):
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.file = self.path.open("a+b")
        self.file.seek(0, os.SEEK_END)
        if self.file.tell() == 0:
            self.file.write(b"0")
            self.file.flush()
        deadline = time.monotonic() + self.timeout
        try:
            while True:
                try:
                    self.file.seek(0)
                    if os.name == "nt":
                        import msvcrt
                        msvcrt.locking(self.file.fileno(), msvcrt.LK_NBLCK, 1)
                    else:
                        import fcntl
                        fcntl.flock(self.file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                    return self
                except OSError:
                    if time.monotonic() >= deadline:
                        raise RuntimeError("Outra execução está usando o tradutor. Interrompa-a antes de iniciar outra.")
                    time.sleep(0.2)
        except BaseException:
            self.file.close()
            self.file = None
            raise

    def __exit__(self, *args):
        try:
            self.file.seek(0)
            if os.name == "nt":
                import msvcrt
                msvcrt.locking(self.file.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                import fcntl
                fcntl.flock(self.file.fileno(), fcntl.LOCK_UN)
        finally:
            self.file.close()


# Modelos Argos executados diretamente pelo CTranslate2. Não importa o cliente
# Argos completo: não há downloads de segmentadores nem chamadas ocultas na inferência.
ARGOS_INDEX_URL = "https://raw.githubusercontent.com/argosopentech/argospm-index/main/index.json"
ARGOS_MIRROR_URL = "https://data.argosopentech.com/argospm/v1/"


# A escolha fica no notebook. Somente modelos testáveis pelo mesmo executor
# CTranslate2 entram aqui; isso mantém a instalação e a execução previsíveis.
MODELOS_LOCAIS = {
    "nllb_1_3b": {
        "titulo": "NLLB-200 distilled 1.3B",
        "backend": "nllb",
        "repositorio": "facebook/nllb-200-distilled-1.3B",
        "qualidade": "alta; melhor equilíbrio para artigos acadêmicos",
        "velocidade": "média",
        "precisao_recomendada": "float16",
        "feixe": 4,
        "lote": 6,
        "max_tokens": 220,
    },
    "nllb_600m": {
        "titulo": "NLLB-200 distilled 600M",
        "backend": "nllb",
        "repositorio": "facebook/nllb-200-distilled-600M",
        "qualidade": "boa",
        "velocidade": "rápida",
        "precisao_recomendada": "float16",
        "feixe": 4,
        "lote": 10,
        "max_tokens": 220,
    },
    "argos": {
        "titulo": "Argos/OpenNMT",
        "backend": "argos",
        "repositorio": None,
        "qualidade": "razoável; rotas indiretas podem perder precisão",
        "velocidade": "muito rápida",
        "precisao_recomendada": "float32",
        "feixe": 4,
        "lote": 8,
        "max_tokens": 200,
    },
}


# Códigos mais usuais. Para acrescentar outro idioma do NLLB, basta incluir
# aqui o código curto e o código Flores-200 correspondente.
NLLB_LANGUAGE_CODES = {
    "ar": "arb_Arab", "bg": "bul_Cyrl", "ca": "cat_Latn",
    "cs": "ces_Latn", "da": "dan_Latn", "de": "deu_Latn",
    "el": "ell_Grek", "en": "eng_Latn", "es": "spa_Latn",
    "fi": "fin_Latn", "fr": "fra_Latn", "he": "heb_Hebr",
    "hi": "hin_Deva", "hu": "hun_Latn", "id": "ind_Latn",
    "it": "ita_Latn", "ja": "jpn_Jpan", "ko": "kor_Hang",
    "nl": "nld_Latn", "no": "nob_Latn", "pl": "pol_Latn",
    "pt": "por_Latn", "ro": "ron_Latn", "ru": "rus_Cyrl",
    "sv": "swe_Latn", "tr": "tur_Latn", "uk": "ukr_Cyrl",
    "vi": "vie_Latn", "zh": "zho_Hans",
}


def _model_name(value):
    name = str(value or "nllb_1_3b").strip().lower().replace("-", "_").replace(".", "_")
    aliases = {
        "nllb": "nllb_1_3b", "nllb_13b": "nllb_1_3b",
        "nllb_1_3": "nllb_1_3b", "nllb_600": "nllb_600m",
        "local": "nllb_1_3b", "offline": "nllb_1_3b",
    }
    name = aliases.get(name, name)
    if name not in MODELOS_LOCAIS:
        raise ValueError("modelo_local deve ser 'nllb_1_3b', 'nllb_600m' ou 'argos'.")
    return name


def listar_modelos_locais():
    """Mostra as escolhas aceitas pelo notebook e devolve seus metadados."""
    print("Modelo         Qualidade                                           Velocidade")
    print("-------------- --------------------------------------------------- ----------")
    for name, spec in MODELOS_LOCAIS.items():
        marker = " (recomendado)" if name == "nllb_1_3b" else ""
        print(f"{name:<14}{spec['qualidade']:<52}{spec['velocidade']}{marker}")
    return {name: dict(spec) for name, spec in MODELOS_LOCAIS.items()}


def _model_directory(directory=None):
    return Path(directory).expanduser().resolve() if directory else Path.home() / ".tradutor_pdf" / "modelos_locais"


def _local_language(value):
    code = str(value).lower().strip().replace("_", "-")
    return {"pt-br": "pb", "pt-pt": "pt", "english": "en", "french": "fr"}.get(code, code)


def _version_tuple(value):
    return tuple(int(x) for x in re.findall(r"\d+", str(value)))


def _installed_models(directory=None):
    packages = []
    for metadata in sorted(_model_directory(directory).glob("*/metadata.json")):
        if metadata.parent.name.startswith("instalando_"):
            continue
        try:
            item = json.loads(metadata.read_text(encoding="utf-8"))
            root = metadata.parent
            if ((root / "model" / "model.bin").is_file()
                    and (root / "sentencepiece.model").is_file()
                    and item.get("from_code") and item.get("to_code")):
                item["path"] = str(root)
                packages.append(item)
        except (OSError, ValueError):
            continue
    return packages


def _model_route(packages, source, target):
    source, target = _local_language(source), _local_language(target)
    if source == target:
        return []
    newest = {}
    for item in packages:
        key = (item.get("from_code"), item.get("to_code"))
        if key not in newest or _version_tuple(item.get("package_version")) > _version_tuple(newest[key].get("package_version")):
            newest[key] = item
    queue, seen = [(source, [])], {source}
    for code, route in queue:
        for (start, end), item in newest.items():
            if start != code or end in seen:
                continue
            extended = route + [item]
            if end == target:
                return extended
            seen.add(end)
            queue.append((end, extended))
    return None


def instalar_pacote_local(arquivo, *, pasta_modelos=None):
    """Instala um arquivo .argosmodel já baixado, sem rede nem execução de código."""
    directory = _model_directory(pasta_modelos)
    directory.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(arquivo) as archive:
        members = archive.infolist()
        if sum(x.file_size for x in members) > 2_000_000_000:
            raise ValueError("Pacote local muito grande para este instalador.")
        for entry in members:
            path = PurePosixPath(entry.filename)
            mode = (entry.external_attr >> 16) & 0o170000
            if path.is_absolute() or ".." in path.parts or "\\" in entry.filename or ":" in entry.filename or mode == 0o120000:
                raise ValueError("Pacote contém caminho inseguro ou link simbólico.")
        metadatas = [x for x in members if x.filename.endswith("/metadata.json") or x.filename == "metadata.json"]
        if len(metadatas) != 1:
            raise ValueError("Pacote Argos sem um metadata.json único.")
        meta_entry = metadatas[0]
        data = json.loads(archive.read(meta_entry))
        source, target = data.get("from_code", ""), data.get("to_code", "")
        version = str(data.get("package_version", "1"))
        if not re.fullmatch(r"[a-z]{2,5}", source) or not re.fullmatch(r"[a-z]{2,5}", target):
            raise ValueError("Códigos de idioma inválidos no pacote.")
        root = PurePosixPath(meta_entry.filename).parent
        name = f"{source}_{target}_{re.sub(r'[^a-zA-Z0-9_-]', '_', version)}"
        destination = directory / name
        if (destination / "metadata.json").is_file() and (destination / "model" / "model.bin").is_file() and (destination / "sentencepiece.model").is_file():
            return destination
        staging = Path(tempfile.mkdtemp(prefix="instalando_", dir=directory))
        try:
            for entry in members:
                try:
                    relative = PurePosixPath(entry.filename).relative_to(root)
                except ValueError:
                    continue
                # Só os arquivos necessários à inferência, metadados e licenças.
                if not relative.parts:
                    continue
                wanted = relative.parts[0] in {"model", "metadata.json", "sentencepiece.model"}
                wanted = wanted or relative.name.lower().startswith(("license", "licence", "readme"))
                if not wanted:
                    continue
                local = staging.joinpath(*relative.parts)
                if entry.is_dir():
                    local.mkdir(parents=True, exist_ok=True)
                else:
                    local.parent.mkdir(parents=True, exist_ok=True)
                    with archive.open(entry) as src, local.open("wb") as dst:
                        shutil.copyfileobj(src, dst)
            if not (staging / "model" / "model.bin").is_file() or not (staging / "sentencepiece.model").is_file():
                raise ValueError("Modelo incompatível: são necessários model/model.bin e sentencepiece.model.")
            if destination.exists():
                raise ValueError(f"Instalação incompleta já existe em {destination}. Mova essa pasta e tente novamente.")
            staging.rename(destination)
            return destination
        finally:
            if staging.exists():
                shutil.rmtree(staging)


def _download_model(package, directory):
    links = [x for x in package.get("links", []) if x.startswith("https://")]
    if not links:
        raise RuntimeError("O índice não forneceu um endereço HTTPS para o modelo.")
    filename = Path(urllib.parse.urlparse(links[0]).path).name
    if not re.fullmatch(r"[A-Za-z0-9_.-]+\.argosmodel", filename):
        raise ValueError("Nome de pacote inválido no índice.")
    # Espelho público oficial; nunca usa outro endpoint de tradução.
    mirror = ARGOS_MIRROR_URL + filename
    if mirror not in links:
        links.append(mirror)
    fd, temporary = tempfile.mkstemp(prefix="modelo_", suffix=".argosmodel", dir=directory)
    os.close(fd)
    errors = []
    try:
        for url in links:
            try:
                size, announced = 0, 0
                with urllib.request.urlopen(url, timeout=60) as response, open(temporary, "wb") as stream:
                    while True:
                        block = response.read(1024 * 1024)
                        if not block:
                            break
                        size += len(block)
                        if size > 1_000_000_000:
                            raise ValueError("Download maior que o limite de 1 GB por pacote.")
                        stream.write(block)
                        if size - announced >= 25 * 1024 * 1024:
                            print(f"  {filename}: {size / 1024**2:.0f} MiB recebidos", flush=True)
                            announced = size
                # Confere o par antes de instalar um pacote recebido da rede.
                with zipfile.ZipFile(temporary) as archive:
                    metadata = next(n for n in archive.namelist() if n.endswith("/metadata.json") or n == "metadata.json")
                    actual = json.loads(archive.read(metadata))
                    if (actual.get("from_code"), actual.get("to_code")) != (package["from_code"], package["to_code"]):
                        raise ValueError("O idioma do pacote recebido difere do solicitado.")
                return instalar_pacote_local(temporary, pasta_modelos=directory)
            except (urllib.error.URLError, OSError, ValueError, zipfile.BadZipFile, StopIteration) as exc:
                errors.append(f"{urllib.parse.urlparse(url).hostname}: {type(exc).__name__}: {exc}")
        raise RuntimeError("Não consegui baixar o modelo. Tente novamente com internet disponível. " + " | ".join(errors))
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def preparar_modelos_locais(idiomas_origem=("en", "fr"), idioma_destino="pt", *, pasta_modelos=None):
    """Prepara os pacotes Argos. Mantida para compatibilidade.

    Ex.: preparar_modelos_locais(["en", "fr"], "pt")
    A tradução em si nunca chama esta função nem baixa modelos automaticamente.
    """
    sources = [idiomas_origem] if isinstance(idiomas_origem, str) else list(idiomas_origem)
    sources = list(dict.fromkeys(_local_language(s) for s in sources))
    target = _local_language(idioma_destino)
    if not sources or "auto" in sources or target == "auto":
        raise ValueError("Informe os idiomas que deseja instalar, como ['en', 'fr'] e destino 'pt'.")
    directory = _model_directory(pasta_modelos)
    directory.mkdir(parents=True, exist_ok=True)
    with _FileLock(directory / "instalacao.lock", timeout=0):
        installed = _installed_models(directory)
        missing = [source for source in sources if _model_route(installed, source, target) is None]
        if missing:
            print("Consultando o índice oficial de modelos Argos...", flush=True)
            with urllib.request.urlopen(ARGOS_INDEX_URL, timeout=30) as response:
                index = json.loads(response.read(5_000_001))
            if not isinstance(index, list):
                raise ValueError("Índice de modelos inválido.")
            for source in missing:
                route = _model_route(index, source, target)
                if route is None:
                    raise ValueError(f"Não há rota de modelos para {source} → {target} no índice.")
                for package in route:
                    if _model_route(_installed_models(directory), package['from_code'], package['to_code']) is not None:
                        continue
                    print(f"Instalando {package['from_code']} → {package['to_code']}...", flush=True)
                    _download_model(package, directory)
        installed = _installed_models(directory)
        for source in sources:
            route = _model_route(installed, source, target)
            print("Modelo pronto: " + " → ".join([source] + [p['to_code'] for p in route]))
    return directory


def _hf_model_directory(model_name, quantization, directory=None):
    root = _model_directory(directory)
    safe_quantization = re.sub(r"[^a-z0-9_]+", "_", str(quantization).lower())
    return root / f"hf_{model_name}_{safe_quantization}"


def _valid_hf_model_directory(path, model_name=None):
    path = Path(path)
    metadata = path / "metadata.json"
    try:
        data = json.loads(metadata.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return False
    return (
        (path / "model" / "model.bin").is_file()
        and (path / "tokenizer").is_dir()
        and (model_name is None or data.get("modelo") == model_name)
    )


def preparar_modelo_local(
    modelo="nllb_1_3b",
    idiomas_origem=DEFAULT_MIXED_LANGUAGES,
    idioma_destino="pt",
    *,
    pasta_modelos=None,
    quantizacao="float16",
):
    """Baixa e prepara uma escolha local. Execute uma vez com internet.

    NLLB usa um único modelo para todos os idiomas. Argos instala uma rota por
    idioma e pode recorrer ao inglês. A tradução posterior não baixa arquivos.
    """
    name = _model_name(modelo)
    spec = MODELOS_LOCAIS[name]
    sources = [idiomas_origem] if isinstance(idiomas_origem, str) else list(idiomas_origem)
    sources = list(dict.fromkeys(_local_language(code) for code in sources))
    target = _local_language(idioma_destino)
    sources = [code for code in sources if code != target]
    if not sources:
        raise ValueError("Inclua ao menos um idioma de origem diferente do destino.")

    if spec["backend"] == "argos":
        return preparar_modelos_locais(sources, target, pasta_modelos=pasta_modelos)

    unsupported = [code for code in [*sources, target] if code not in NLLB_LANGUAGE_CODES]
    if unsupported:
        raise ValueError(
            "Falta mapear no módulo o código NLLB de: " + ", ".join(sorted(set(unsupported)))
        )
    quantization = str(quantizacao or spec["precisao_recomendada"]).strip().lower()
    allowed = {"float16", "float32", "int8_float16", "int8_float32"}
    if quantization not in allowed:
        raise ValueError("quantizacao: float16, float32, int8_float16 ou int8_float32.")

    destination = _hf_model_directory(name, quantization, pasta_modelos)
    destination.parent.mkdir(parents=True, exist_ok=True)
    if _valid_hf_model_directory(destination, name):
        print(f"Modelo já preparado: {spec['titulo']} | {quantization} | {destination}")
        return destination

    lock_path = destination.parent / f"preparacao_{name}_{quantization}.lock"
    with _FileLock(lock_path, timeout=0):
        if _valid_hf_model_directory(destination, name):
            print(f"Modelo já preparado: {spec['titulo']} | {quantization} | {destination}")
            return destination
        try:
            import ctranslate2
            from transformers import AutoTokenizer
        except ImportError as exc:
            raise ImportError(
                "Execute a célula de instalação do notebook antes de preparar o NLLB."
            ) from exc

        staging = Path(tempfile.mkdtemp(prefix=f"preparando_{name}_", dir=destination.parent))
        try:
            print(f"Baixando e convertendo {spec['titulo']} ({quantization}). Isso ocorre uma única vez.")
            model_dir = staging / "model"
            tokenizer_dir = staging / "tokenizer"
            class _SafeTensorsConverter(ctranslate2.converters.TransformersConverter):
                """Evita o checkpoint pickle mesmo em versões antigas do PyTorch."""

                def load_model(self, model_class, model_name_or_path, **kwargs):
                    kwargs["use_safetensors"] = True
                    return model_class.from_pretrained(model_name_or_path, **kwargs)

            converter = _SafeTensorsConverter(
                spec["repositorio"],
                load_as_float16=quantization in {"float16", "int8_float16"},
                low_cpu_mem_usage=True,
            )
            converter.convert(str(model_dir), quantization=quantization)
            tokenizer = AutoTokenizer.from_pretrained(spec["repositorio"])
            tokenizer.save_pretrained(tokenizer_dir)
            metadata = {
                "formato": 1,
                "modelo": name,
                "titulo": spec["titulo"],
                "backend": spec["backend"],
                "repositorio": spec["repositorio"],
                "quantizacao": quantization,
                "preparado_em": datetime.now(timezone.utc).isoformat(),
            }
            (staging / "metadata.json").write_text(
                json.dumps(metadata, ensure_ascii=False, indent=2), encoding="utf-8"
            )
            if not _valid_hf_model_directory(staging, name):
                raise RuntimeError("A conversão terminou sem produzir todos os arquivos esperados.")
            if destination.exists():
                raise RuntimeError(
                    f"Existe uma preparação incompleta em {destination}. Renomeie essa pasta e tente novamente."
                )
            staging.rename(destination)
            print(f"Modelo pronto: {spec['titulo']} | {quantization} | {destination}")
            return destination
        finally:
            if staging.exists():
                shutil.rmtree(staging)


class LocalTranslator:
    """Inferência Argos sem rede, mantida como opção leve."""
    def __init__(self, source, target, directory=None, compute_type="float32", threads=4,
                 device="cpu", beam_size=None, batch_size=None):
        self.source, self.target = _local_language(source), _local_language(target)
        if self.source == "auto":
            raise ValueError("O idioma precisa ser identificado antes de iniciar o motor local.")
        self.route = _model_route(_installed_models(directory), self.source, self.target)
        if self.route is None:
            raise RuntimeError(f"Falta modelo local para {source} → {target}. Execute primeiro "
                               f"preparar_modelos_locais('{source}', '{target}').")
        try:
            import ctranslate2
            import sentencepiece
        except ImportError as exc:
            raise ImportError("Instale no Jupyter: %pip install pymupdf ctranslate2 sentencepiece langid") from exc
        if compute_type not in {"float16", "float32", "int8", "int8_float16", "int8_float32", "default", "auto"}:
            raise ValueError("precisao_local inválida para o CTranslate2.")
        self.ct2, self.spm = ctranslate2, sentencepiece
        self.compute_type = compute_type
        self.threads = max(1, int(threads))
        self.beam_size = max(1, int(beam_size or MODELOS_LOCAIS["argos"]["feixe"]))
        self.batch_size = max(1, int(batch_size or MODELOS_LOCAIS["argos"]["lote"]))
        self.model_name = "argos"
        self.provider_label = "Argos"
        self.requested_device = str(device).lower().strip()
        if self.requested_device not in {"cpu", "cuda", "auto"}:
            raise ValueError("dispositivo_local: cpu, cuda ou auto.")
        self.device = "cpu"
        if self.requested_device != "cpu":
            try:
                available = self.ct2.get_cuda_device_count() > 0
            except RuntimeError as exc:
                if self.requested_device == "cuda":
                    raise RuntimeError("Não foi possível inicializar CUDA. Use dispositivo_local='cpu'.") from exc
                available = False
            if available:
                self.device = "cuda"
            elif self.requested_device == "cuda":
                raise RuntimeError("Nenhuma GPU CUDA disponível. Use dispositivo_local='cpu' ou 'auto'.")
        self.recovery_stats = {"tentativas_recuperacao_local": 0,
                               "fragmentos_recuperados_locais": 0,
                               "trocas_cuda_cpu": 0}
        self.loaded = {}
        specs = [(p['from_code'], p['to_code'], p.get('package_version')) for p in self.route]
        self.namespace = hashlib.sha256(json.dumps(["ct2-argos-v1", specs, compute_type]).encode()).hexdigest()[:16]
        self.route_label = " → ".join([self.source] + [p['to_code'] for p in self.route])

    def _load(self, package):
        path = package['path']
        if path not in self.loaded:
            root = Path(path)
            processor = self.spm.SentencePieceProcessor(model_file=str(root / "sentencepiece.model"))
            try:
                engine = self.ct2.Translator(str(root / "model"), device=self.device,
                                            compute_type=self.compute_type, inter_threads=1,
                                            intra_threads=self.threads)
            except RuntimeError as exc:
                if not self._fallback_cuda_to_cpu(exc):
                    raise
                engine = self.ct2.Translator(str(root / "model"), device="cpu",
                                            compute_type=self.compute_type, inter_threads=1,
                                            intra_threads=self.threads)
            self.loaded[path] = (processor, engine)
            print(f"Modelo carregado: {package['from_code']} → {package['to_code']} | "
                  f"{self.device.upper()} | {engine.compute_type}")
        return self.loaded[path]

    def _fallback_cuda_to_cpu(self, exc):
        """Troca automática inclusive quando a falha CUDA aparece no primeiro lote.

        O CTranslate2 pode construir o objeto CUDA antes de tentar carregar cuBLAS;
        no Windows, a ausência de cublas64_12.dll só aparece em translate_batch.
        """
        if self.requested_device != "auto" or self.device != "cuda":
            return False
        print(f"CUDA indisponível durante a execução; recriando o modelo na CPU. Motivo: {exc}")
        self.loaded.clear()
        self.device = "cpu"
        self.recovery_stats["trocas_cuda_cpu"] += 1
        return True

    def _translate_batch(self, package, chunks, **options):
        processor, engine = self._load(package)
        try:
            return processor, engine.translate_batch(chunks, **options)
        except RuntimeError as exc:
            if self._fallback_cuda_to_cpu(exc):
                processor, engine = self._load(package)
                # Uma única repetição na CPU. Se falhar, o erro real é propagado.
                return processor, engine.translate_batch(chunks, **options)
            if self.device == "cuda":
                raise RuntimeError(
                    f"Falha ao executar na GPU CUDA: {exc}. "
                    "Use dispositivo_local='cpu' ou corrija a instalação CUDA.") from exc
            raise

    @staticmethod
    def _decode(prediction, processor, prefix):
        hypotheses = prediction.hypotheses
        tokens = list(hypotheses[0]) if hypotheses else []
        if len(tokens) >= 512:
            raise LocalChunkError("O modelo local atingiu o limite de saída; resposta incompleta recusada.")
        if prefix and tokens and tokens[0] == prefix:
            tokens = tokens[1:]
        decoded = processor.decode_pieces(tokens).replace("▁", " ").strip()
        if not _valid_cached_translation(decoded):
            raise LocalChunkError("O modelo local devolveu tradução vazia ou inválida.")
        return decoded

    def _recover(self, tokens, package, prefix, budget, depth=0):
        # No máximo 12 chamadas extras por etapa do modelo e 3 subdivisões.
        # Nunca cacheia uma resposta parcial como tradução completa.
        if budget[0] <= 0:
            raise LocalChunkError("Limite de recuperação local atingido; trecho mantido como pendência.")
        budget[0] -= 1
        self.recovery_stats["tentativas_recuperacao_local"] += 1
        processor, predictions = self._translate_batch(
            package,
            [tokens], target_prefix=[[prefix]] if prefix else None,
            beam_size=1, num_hypotheses=1, length_penalty=1.0,
            max_batch_size=1, max_input_length=0, max_decoding_length=512,
            min_decoding_length=1, replace_unknowns=True)
        if len(predictions) != 1:
            raise RuntimeError("O motor local retornou quantidade inesperada de respostas.")
        try:
            return self._decode(predictions[0], processor, prefix)
        except LocalChunkError as exc:
            # Prefere fronteiras de palavras; não divide dentro de uma palavra.
            boundaries = [i for i in range(1, len(tokens)) if tokens[i].startswith("▁")
                          and len(tokens) / 4 <= i <= 3 * len(tokens) / 4]
            if depth >= 3 or not boundaries or budget[0] < 2:
                raise LocalChunkError(
                    "O modelo não traduziu o trecho mesmo após recuperação limitada. "
                    "O original foi preservado para revisão.") from exc
            middle = min(boundaries, key=lambda i: abs(i - len(tokens) / 2))
            left = self._recover(tokens[:middle], package, prefix, budget, depth + 1)
            right = self._recover(tokens[middle:], package, prefix, budget, depth + 1)
            return left + " " + right

    def _step(self, text, package):
        processor, _ = self._load(package)
        sentences = re.split(r'(?<=[.!?])\s+(?=[A-ZÀ-ÖØ-Þ0-9“"(])', text.strip())
        chunks = []
        for sentence in sentences:
            tokens = processor.encode(sentence, out_type=str)
            while len(tokens) > 200:
                boundary = 200
                # Prefere um início de palavra; não descarta tokens da entrada.
                for i in range(199, 100, -1):
                    if tokens[i].startswith("▁"):
                        boundary = i
                        break
                chunks.append(tokens[:boundary])
                tokens = tokens[boundary:]
            if tokens:
                chunks.append(tokens)
        if not chunks:
            raise LocalChunkError("O trecho não produziu tokens para tradução.")
        prefix = package.get('target_prefix', '')
        processor, predictions = self._translate_batch(
            package,
            chunks, target_prefix=[[prefix]] * len(chunks) if prefix else None,
            beam_size=self.beam_size, num_hypotheses=1, length_penalty=1.0,
            max_batch_size=self.batch_size, max_input_length=0, max_decoding_length=512,
            replace_unknowns=True)
        if len(predictions) != len(chunks):
            raise RuntimeError("O motor local retornou quantidade inesperada de respostas.")
        pieces, budget = [], [12]
        for chunk, prediction in zip(chunks, predictions):
            try:
                decoded = self._decode(prediction, processor, prefix)
            except LocalChunkError:
                print("   [Local] Resposta inválida; tentando recuperação e partes menores.")
                decoded = self._recover(chunk, package, prefix, budget)
                self.recovery_stats["fragmentos_recuperados_locais"] += 1
            pieces.append(decoded)
        return " ".join(pieces)

    def translate(self, text):
        for package in self.route:
            text = self._step(text, package)
        if not _valid_cached_translation(text):
            raise LocalChunkError("O modelo local não produziu uma resposta válida.")
        return normalize_spaces(text)


class NLLBTranslator:
    """NLLB convertido para CTranslate2, com tradução direta entre idiomas."""

    def __init__(self, source, target, model_name="nllb_1_3b", directory=None,
                 quantization="float16", compute_type="float16", threads=4,
                 device="cpu", beam_size=None, batch_size=None):
        self.source, self.target = _local_language(source), _local_language(target)
        self.model_name = _model_name(model_name)
        self.spec = MODELOS_LOCAIS[self.model_name]
        if self.spec["backend"] != "nllb":
            raise ValueError("NLLBTranslator recebeu um modelo de outro backend.")
        missing = [code for code in (self.source, self.target) if code not in NLLB_LANGUAGE_CODES]
        if missing:
            raise ValueError("Idioma ainda não mapeado para NLLB: " + ", ".join(missing))

        self.quantization = str(quantization or self.spec["precisao_recomendada"]).lower().strip()
        self.root = _hf_model_directory(self.model_name, self.quantization, directory)
        if not _valid_hf_model_directory(self.root, self.model_name):
            raise RuntimeError(
                f"Falta preparar {self.model_name} com quantização {self.quantization}. "
                "Execute primeiro preparar_modelo_local(...) na célula de download."
            )
        try:
            import ctranslate2
            from transformers import AutoTokenizer
        except ImportError as exc:
            raise ImportError("Execute a célula de instalação do notebook.") from exc

        allowed_compute = {"float16", "float32", "int8", "int8_float16",
                           "int8_float32", "default", "auto"}
        if compute_type not in allowed_compute:
            raise ValueError("precisao_local inválida para o CTranslate2.")
        self.ct2 = ctranslate2
        self.AutoTokenizer = AutoTokenizer
        self.compute_type = compute_type
        self.threads = max(1, int(threads))
        self.beam_size = max(1, int(beam_size or self.spec["feixe"]))
        self.batch_size = max(1, int(batch_size or self.spec["lote"]))
        self.max_tokens = int(self.spec["max_tokens"])
        self.requested_device = str(device).lower().strip()
        if self.requested_device not in {"cpu", "cuda", "auto"}:
            raise ValueError("dispositivo_local: cpu, cuda ou auto.")
        self.device = "cpu"
        if self.requested_device != "cpu":
            try:
                available = self.ct2.get_cuda_device_count() > 0
            except RuntimeError as exc:
                if self.requested_device == "cuda":
                    raise RuntimeError("Não foi possível inicializar CUDA.") from exc
                available = False
            if available:
                self.device = "cuda"
            elif self.requested_device == "cuda":
                raise RuntimeError("Nenhuma GPU CUDA disponível.")

        self.recovery_stats = {
            "tentativas_recuperacao_local": 0,
            "fragmentos_recuperados_locais": 0,
            "saidas_incompletas_detectadas": 0,
            "trocas_cuda_cpu": 0,
        }
        self.loaded = {}
        metadata = json.loads((self.root / "metadata.json").read_text(encoding="utf-8"))
        # v2 invalida traduções antigas que poderiam terminar no primeiro
        # período de um parágrafo com várias sentenças.
        identity = ["ct2-hf-v2-sentences", metadata, compute_type, self.beam_size]
        self.namespace = hashlib.sha256(
            json.dumps(identity, sort_keys=True).encode("utf-8")
        ).hexdigest()[:16]
        short_title = "NLLB 1.3B" if self.model_name == "nllb_1_3b" else "NLLB 600M"
        self.provider_label = short_title
        self.route_label = f"{short_title}: {self.source} → {self.target} (direto)"
        self.route = [{"from_code": self.source, "to_code": self.target,
                       "model_name": self.model_name}]

    def _fallback_cuda_to_cpu(self, exc):
        if self.requested_device != "auto" or self.device != "cuda":
            return False
        print(f"CUDA indisponível; recriando o modelo na CPU. Motivo: {exc}")
        self.loaded.clear()
        self.device = "cpu"
        self.recovery_stats["trocas_cuda_cpu"] += 1
        return True

    def _load(self):
        key = str(self.root)
        if key not in self.loaded:
            tokenizer = self.AutoTokenizer.from_pretrained(
                str(self.root / "tokenizer"), local_files_only=True
            )
            execution_type = self.compute_type
            if self.device == "cpu" and execution_type in {"float16", "int8_float16"}:
                execution_type = "auto"
            try:
                engine = self.ct2.Translator(
                    str(self.root / "model"), device=self.device,
                    compute_type=execution_type, inter_threads=1,
                    intra_threads=self.threads,
                )
            except RuntimeError as exc:
                if not self._fallback_cuda_to_cpu(exc):
                    raise
                engine = self.ct2.Translator(
                    str(self.root / "model"), device="cpu", compute_type="auto",
                    inter_threads=1, intra_threads=self.threads,
                )
            self.loaded[key] = (tokenizer, engine)
            print(f"Modelo carregado: {self.spec['titulo']} | {self.device.upper()} | {engine.compute_type}")
        return self.loaded[key]

    def _encode(self, tokenizer, text):
        source_code = NLLB_LANGUAGE_CODES[self.source]
        tokenizer.src_lang = source_code
        # Algumas versões do Transformers não recompõem os marcadores
        # especiais apenas com a atribuição acima.
        set_source = getattr(tokenizer, "set_src_lang_special_tokens", None)
        if callable(set_source):
            set_source(source_code)
        ids = tokenizer.encode(text, add_special_tokens=True)
        return tokenizer.convert_ids_to_tokens(ids)

    def _token_count(self, tokenizer, text):
        return len(self._encode(tokenizer, text))

    def _split_for_model(self, text, tokenizer):
        # O NLLB é mais confiável com uma sentença por entrada. O lote ainda
        # envia várias sentenças de uma vez à GPU, mas elas não são fundidas.
        sentences = [piece.strip() for piece in re.split(
            r'(?<=[.!?])\s+(?=[A-ZÀ-ÖØ-Þ0-9“"(•●▪◦‣])', text.strip()) if piece.strip()]
        if not sentences:
            sentences = [text.strip()]
        small = []
        for sentence in sentences:
            if self._token_count(tokenizer, sentence) <= self.max_tokens:
                small.append(sentence)
                continue
            words, current = sentence.split(), []
            for word in words:
                candidate = " ".join([*current, word])
                if current and self._token_count(tokenizer, candidate) > self.max_tokens:
                    small.append(" ".join(current))
                    current = [word]
                else:
                    current.append(word)
            if current:
                small.append(" ".join(current))
        return small

    def _translate_batch(self, chunks, beam_size=None):
        tokenizer, engine = self._load()
        encoded = [self._encode(tokenizer, chunk) for chunk in chunks]
        prefix = NLLB_LANGUAGE_CODES[self.target]
        options = dict(
            target_prefix=[[prefix]] * len(encoded),
            beam_size=max(1, int(beam_size or self.beam_size)),
            num_hypotheses=1,
            length_penalty=1.0,
            max_batch_size=self.batch_size,
            max_input_length=0,
            max_decoding_length=512,
            min_decoding_length=1,
            replace_unknowns=True,
        )
        try:
            predictions = engine.translate_batch(encoded, **options)
        except RuntimeError as exc:
            if not self._fallback_cuda_to_cpu(exc):
                if self.device == "cuda":
                    raise RuntimeError(
                        f"Falha ao executar na GPU CUDA: {exc}. "
                        "Use dispositivo_local='cpu' ou corrija a instalação CUDA."
                    ) from exc
                raise
            tokenizer, engine = self._load()
            predictions = engine.translate_batch(encoded, **options)
        return tokenizer, predictions, prefix

    @staticmethod
    def _decode(prediction, tokenizer, prefix):
        hypotheses = prediction.hypotheses
        tokens = list(hypotheses[0]) if hypotheses else []
        if len(tokens) >= 512:
            raise LocalChunkError("O modelo local atingiu o limite de saída.")
        if prefix in tokens:
            tokens.remove(prefix)
        ids = tokenizer.convert_tokens_to_ids(tokens)
        decoded = tokenizer.decode(ids, skip_special_tokens=True).strip()
        if not _valid_cached_translation(decoded):
            raise LocalChunkError("O modelo local devolveu tradução vazia ou inválida.")
        return decoded

    def _ensure_complete(self, source_text, translated_text):
        source_words = re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ]+", source_text)
        target_words = re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ]+", translated_text)
        source_count = len(source_words)
        minimum_ratio = 0.48 if source_count >= 18 else (0.30 if source_count >= 9 else None)
        if minimum_ratio is not None and len(target_words) / source_count < minimum_ratio:
            self.recovery_stats["saidas_incompletas_detectadas"] += 1
            raise LocalChunkError(
                f"Tradução possivelmente incompleta ({len(target_words)}/"
                f"{len(source_words)} palavras); refazendo em partes menores."
            )
        return translated_text

    def _recover(self, text, budget, depth=0):
        if budget[0] <= 0:
            raise LocalChunkError("Limite de recuperação local atingido.")
        budget[0] -= 1
        self.recovery_stats["tentativas_recuperacao_local"] += 1
        tokenizer, predictions, prefix = self._translate_batch([text], beam_size=1)
        try:
            decoded = self._decode(predictions[0], tokenizer, prefix)
            return self._ensure_complete(text, decoded)
        except (LocalChunkError, IndexError) as exc:
            words = text.split()
            if depth >= 3 or len(words) < 4 or budget[0] < 2:
                raise LocalChunkError(
                    "O modelo não traduziu o trecho; o original foi preservado para revisão."
                ) from exc
            middle = len(words) // 2
            left = self._recover(" ".join(words[:middle]), budget, depth + 1)
            right = self._recover(" ".join(words[middle:]), budget, depth + 1)
            return left + " " + right

    def translate(self, text):
        tokenizer, _ = self._load()
        chunks = self._split_for_model(text, tokenizer)
        if not chunks:
            raise LocalChunkError("O trecho não produziu tokens para tradução.")
        tokenizer, predictions, prefix = self._translate_batch(chunks)
        if len(predictions) != len(chunks):
            raise RuntimeError("O motor local retornou quantidade inesperada de respostas.")
        pieces = []
        for chunk, prediction in zip(chunks, predictions):
            try:
                decoded = self._decode(prediction, tokenizer, prefix)
                decoded = self._ensure_complete(chunk, decoded)
            except LocalChunkError as exc:
                print(f"   [Local] {exc}")
                decoded = self._recover(chunk, [10])
                self.recovery_stats["fragmentos_recuperados_locais"] += 1
            pieces.append(decoded)
        result = normalize_spaces(" ".join(pieces))
        if not _valid_cached_translation(result):
            raise LocalChunkError("O modelo local não produziu uma resposta válida.")
        return result


def _build_local_translator(source, target, model_name, model_dir, quantization,
                            compute_type, threads, device, beam_size, batch_size):
    name = _model_name(model_name)
    if name == "argos":
        return LocalTranslator(
            source, target, model_dir, compute_type, threads, device,
            beam_size=beam_size, batch_size=batch_size,
        )
    return NLLBTranslator(
        source, target, name, model_dir, quantization, compute_type, threads,
        device, beam_size=beam_size, batch_size=batch_size,
    )


def is_standalone_math(text):
    """Reconhece apenas notação isolada simples, sem remover fórmulas de prosa.

    Classificação deliberadamente conservadora: casos incertos passam pelo
    tradutor e, se necessário, pela recuperação. O texto do PDF nunca é apagado.
    """
    if not re.search(r"[=⇒⇔∫∑√≤≥]", text):
        return False
    words = re.findall(r"[^\W\d_]+", text, flags=re.UNICODE)
    function = r"(?:arcsin|arccos|arctan|sin|cos|tan|log|ln|exp|lim)"
    variable = r"[a-zA-Zα-ωΑ-Ω]"
    atom = rf"(?:{function}|{variable}|d{variable}|(?:{function})?{variable}d{variable}|{function}{variable})"
    return all(re.fullmatch(atom, word) for word in words)


_LANGUAGE_IDENTIFIERS = {}


def detectar_idioma_local(texto, idiomas=None, minimo_letras=30):
    """Detecção local com o modelo embutido no langid, sem acesso à internet."""
    sample = normalize_spaces(texto)[:15000]
    if sum(c.isalpha() for c in sample) < int(minimo_letras):
        raise ValueError("Pouco texto para identificar o idioma. Informe idioma_origem='en' ou 'fr'.")
    try:
        from langid.langid import LanguageIdentifier, model
    except ImportError as exc:
        raise ImportError("Para detectar o idioma sem rede: %pip install langid") from exc
    allowed = tuple(dict.fromkeys(str(code).strip().lower() for code in (idiomas or ()) if str(code).strip()))
    key = allowed or ("*",)
    identifier = _LANGUAGE_IDENTIFIERS.get(key)
    if identifier is None:
        identifier = LanguageIdentifier.from_modelstring(model, norm_probs=True)
        if allowed:
            identifier.set_languages(list(allowed))
        _LANGUAGE_IDENTIFIERS[key] = identifier
    code, score = identifier.rank(sample)[0]
    return code, float(score)


_LANGUAGE_HEADING_HINTS = {
    "en": ("abstract", "keywords", "key words"),
    "fr": ("résumé", "resume", "mots-clés", "mots cles"),
    "it": ("riassunto", "parole chiave"),
    "pt": ("resumo", "palavras-chave", "palavras chave"),
    "es": ("resumen", "palabras clave"),
    "de": ("zusammenfassung", "schlüsselwörter", "schlusselworter"),
}


def _detectar_idioma_do_trecho(texto, idiomas, predominante):
    """Combina evidência do trecho com o idioma predominante do documento."""
    sample = normalize_spaces(texto)
    lowered = sample.casefold().lstrip("0123456789.:-–—()[] ")
    for code in idiomas:
        if any(lowered.startswith(hint) for hint in _LANGUAGE_HEADING_HINTS.get(code, ())):
            return code, 1.0, "cabecalho"

    letters = sum(char.isalpha() for char in sample)
    try:
        code, score = detectar_idioma_local(sample, idiomas, minimo_letras=8)
    except ValueError:
        return predominante, None, "predominante_texto_curto"

    # Textos longos precisam de confiança moderada; textos médios, de
    # confiança alta. Fragmentos curtos herdam o idioma global do documento.
    if (letters >= 40 and score >= 0.80) or (letters >= 15 and score >= 0.96):
        return code, score, "estatistica_trecho"
    return predominante, score, "predominante_baixa_confianca"


def _source_from_pdf(path, password, pages, start, end):
    interval = _interpretar_paginas(pages)
    if interval:
        start, end = interval
    with fitz.open(path) as doc:
        if doc.needs_pass and (not password or not doc.authenticate(password)):
            raise ValueError("PDF protegido: informe senha='sua senha'.")
        last = min(len(doc), int(end)) if end is not None else len(doc)
        first = int(start) - 1
        if first < 0 or first >= last:
            raise ValueError("Intervalo de páginas inválido.")
        # Mais de uma página reduz a influência de um resumo em outro idioma.
        sample = "\n".join(doc[i].get_text()[:5000] for i in range(first, min(last, first + 4)))
    code, score = detectar_idioma_local(sample)
    print(f"Idioma identificado localmente: {code}. Se estiver incorreto, informe idioma_origem explicitamente.")
    return code


def _dominant_source_from_pdf(path, password, pages, start, end, idiomas):
    """Amostra todas as páginas solicitadas para obter o idioma predominante."""
    interval = _interpretar_paginas(pages)
    if interval:
        start, end = interval
    pieces, used = [], 0
    with fitz.open(path) as doc:
        if doc.needs_pass and (not password or not doc.authenticate(password)):
            raise ValueError("PDF protegido: informe senha='sua senha'.")
        last = min(len(doc), int(end)) if end is not None else len(doc)
        first = int(start) - 1
        if first < 0 or first >= last:
            raise ValueError("Intervalo de páginas inválido.")
        for index in range(first, last):
            text = doc[index].get_text()
            if not text:
                continue
            excerpt = text[:2500]
            pieces.append(excerpt)
            used += len(excerpt)
            if used >= 100000:
                break
    sample = "\n".join(pieces)
    code, score = detectar_idioma_local(sample, idiomas, minimo_letras=30)
    return code, score


def _translation_mode(value):
    value = str(value or "local").lower().strip().replace("-", "_")
    if value in {"local", "offline", "nllb", "argos"}:
        return "local"
    raise ValueError("Esta versão funciona somente no modo local/offline.")


class HybridTranslator:
    """Camada local com cache. O nome é mantido por compatibilidade."""

    def __init__(self, source, target, mode="local", timeout=25, interval=3,
                 cooldown=900, state_dir=None, attempts=1, max_wait=60,
                 model_dir=None, compute_type="float16", threads=4,
                 device="auto",
                 model_name="nllb_1_3b", quantization="float16",
                 beam_size=None, batch_size=None, portuguese_variant="pt-BR",
                 terminology_profile=None, custom_glossary=None,
                 protect_elements=True):
        self.source, self.target, self.engine = source, target, _translation_mode(mode)
        self.portuguese_variant = _normalizar_variante_portugues(portuguese_variant, target)
        self.terminology_profile = _normalizar_perfil_terminologico(terminology_profile)
        self.custom_glossary = _normalizar_glossario_personalizado(custom_glossary)
        self.protect_elements = bool(protect_elements)
        self.local = _build_local_translator(
            source, target, model_name, model_dir, quantization, compute_type,
            threads, device, beam_size, batch_size,
        )
        self.stats = {"requisicoes": 0, "retentativas": 0,
                      "trechos_cache": 0, "fragmentos_cache": 0,
                      "fragmentos_locais": 0, "fragmentos_locais_cache": 0,
                      "ajustes_glossario": 0, "elementos_protegidos": 0,
                      "recuperacoes_marcadores": 0}
        self.last_providers = []

    def _cached_or_translate(self, text, cache, cache_path):
        base = cache_key(text, self.source, self.target)
        local_key = f"local|{self.local.namespace}|{base}"
        local_cached = cache.get(local_key)
        if _valid_cached_translation(local_cached):
            return local_cached, self.local.provider_label, True
        translated = self.local.translate(text)
        cache[local_key] = translated
        if cache_path:
            save_cache(cache_path, cache)
        return translated, self.local.provider_label, False

    def _protected_or_translate(self, text, cache, cache_path):
        if not self.protect_elements:
            return self._cached_or_translate(text, cache, cache_path)
        masked, elements, segments = proteger_elementos_tecnicos(text)
        if not elements:
            return self._cached_or_translate(text, cache, cache_path)
        self.stats["elementos_protegidos"] += len(elements)
        try:
            result, provider, cached = self._cached_or_translate(masked, cache, cache_path)
            return restaurar_elementos_tecnicos(result, elements), provider, cached
        except (ProtectedElementError, LocalChunkError):
            # Rota de segurança: traduz somente as partes linguísticas e
            # intercala os elementos originais, que nunca são enviados. Isso
            # também cobre modelos que rejeitam o trecho mascarado por inteiro.
            self.stats["recuperacoes_marcadores"] += 1
            pieces, all_cached = [], True
            provider = self.local.provider_label
            for protected, segment in segments:
                if protected or len(re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ]", segment)) < 2:
                    pieces.append(segment)
                    continue
                translated, _, segment_cached = self._cached_or_translate(
                    segment.strip(), cache, cache_path
                )
                prefix = " " if segment[:1].isspace() else ""
                suffix = " " if segment[-1:].isspace() else ""
                pieces.append(prefix + translated.strip() + suffix)
                all_cached = all_cached and segment_cached
            return normalize_spaces("".join(pieces)), provider, all_cached

    def translate_cached(self, text, cache, cache_path=None):
        pieces, providers, all_cached = [], [], True
        for part in split_text(text):
            result, provider, cached = self._protected_or_translate(part, cache, cache_path)
            result, glossary_changes = aplicar_glossario_terminologico(
                part, result, self.source, self.terminology_profile, self.custom_glossary
            )
            self.stats["ajustes_glossario"] += glossary_changes
            pieces.append(result)
            providers.append(provider)
            self.stats["fragmentos_locais"] += 1
            if cached:
                self.stats["fragmentos_cache"] += 1
                self.stats["fragmentos_locais_cache"] += 1
            all_cached = all_cached and cached
        if all_cached and pieces:
            self.stats["trechos_cache"] += 1
        self.last_providers = sorted(set(providers))
        result = " ".join(pieces).strip()
        if self.portuguese_variant == "pt-BR":
            result = normalizar_portugues_brasileiro(result)
        return result

    def translate(self, text):
        return self.translate_cached(text, {})


class MixedTranslator:
    """Seleciona uma rota por trecho e preserva o idioma de destino."""

    def __init__(self, source, target, mode="local", timeout=25, interval=3,
                 cooldown=900, state_dir=None, attempts=1, max_wait=60,
                 model_dir=None, compute_type="float16", threads=4,
                 device="auto",
                 model_name="nllb_1_3b", quantization="float16",
                 beam_size=None, batch_size=None, portuguese_variant="pt-BR",
                 terminology_profile=None, custom_glossary=None,
                 protect_elements=True):
        requested = DEFAULT_MIXED_LANGUAGES if source == "misto" else tuple(source)
        self.sources = tuple(dict.fromkeys([*requested, target]))
        self.source, self.target, self.engine = "misto", target, _translation_mode(mode)
        self.children = {
            code: HybridTranslator(code, target, mode, timeout, interval, cooldown,
                                   state_dir, attempts, max_wait, model_dir,
                                   compute_type, threads, device,
                                   model_name, quantization, beam_size, batch_size,
                                   portuguese_variant, terminology_profile, custom_glossary,
                                   protect_elements)
            for code in self.sources if code != target
        }
        # Os idiomas compartilham a mesma instância NLLB na memória.
        shared_loaded = {}
        for child in self.children.values():
            if child.local:
                child.local.loaded = shared_loaded
        first = next(iter(self.children.values()), None)
        if first is None:
            raise ValueError("O modo misto precisa ter ao menos um idioma diferente do destino.")
        self.local = self
        local_children = [child.local for child in self.children.values() if child.local]
        labels = dict.fromkeys(child.route_label for child in local_children)
        self.route_label = " | ".join(labels)
        self.route = [package for child in local_children for package in child.route]
        self.last_providers = []
        self.last_source = None
        self.last_source_score = None
        self.last_source_reason = None
        self.dominant_source = next((code for code in self.sources if code != target), target)
        self.preserved_target_count = 0

    @property
    def stats(self):
        totals = {}
        for child in self.children.values():
            for key, value in child.stats.items():
                totals[key] = totals.get(key, 0) + value
        totals["fragmentos_idioma_destino_preservados"] = self.preserved_target_count
        return totals

    @property
    def recovery_stats(self):
        totals = {}
        for child in self.children.values():
            if not child.local:
                continue
            for key, value in child.local.recovery_stats.items():
                totals[key] = totals.get(key, 0) + value
        return totals

    @property
    def loaded(self):
        return any(child.local and child.local.loaded for child in self.children.values())

    @property
    def device(self):
        devices = {child.local.device for child in self.children.values() if child.local and child.local.loaded}
        if "cuda" in devices:
            return "cuda"
        if devices:
            return sorted(devices)[0]
        first = next((child.local for child in self.children.values() if child.local), None)
        return first.device if first else None

    def translate_cached(self, text, cache, cache_path=None):
        source, score, reason = _detectar_idioma_do_trecho(
            text, self.sources, self.dominant_source)
        self.last_source, self.last_source_score = source, score
        self.last_source_reason = reason
        if source == self.target:
            self.last_providers = ["Original"]
            self.preserved_target_count += 1
            return normalize_spaces(text)
        child = self.children[source]
        result = child.translate_cached(text, cache, cache_path)
        self.last_providers = child.last_providers[:]
        return result

    def translate(self, text):
        return self.translate_cached(text, {})


def _criar_tradutor(source, target, mode="local", timeout=25, interval=3,
                    cooldown=900, state_dir=None, attempts=1, max_wait=60,
                    model_dir=None, compute_type="float16", threads=4,
                    device="auto",
                    model_name="nllb_1_3b", quantization="float16",
                    beam_size=None, batch_size=None, portuguese_variant="pt-BR",
                    terminology_profile=None, custom_glossary=None,
                    protect_elements=True):
    translator_class = MixedTranslator if _is_mixed_source(source) else HybridTranslator
    return translator_class(source, target, mode, timeout, interval, cooldown,
                            state_dir, attempts, max_wait, model_dir, compute_type,
                            threads, device, model_name,
                            quantization, beam_size, batch_size, portuguese_variant,
                            terminology_profile, custom_glossary, protect_elements)


def testar_traducao(texto, idioma_origem="auto", idioma_destino="pt", *, motor="local",
                    timeout=25, intervalo_requisicoes=3, pausa_429=900, pasta_controle=None,
                    pasta_modelos=None, precisao_local="float16", threads_locais=4,
                    dispositivo_local="auto", modelo_local="nllb_1_3b",
                    quantizacao_modelo="float16", feixe=None, lote_modelo=None,
                    variante_portugues="pt-BR", perfil_terminologico=None,
                    glossario_personalizado=None, proteger_elementos=True):
    mode = _translation_mode(motor)
    source = _normalizar_idioma_origem(idioma_origem)
    if source == "auto":
        source, _ = detectar_idioma_local(texto)
    translator = _criar_tradutor(source, idioma_destino, mode, timeout,
                                 intervalo_requisicoes, pausa_429, pasta_controle,
                                 model_dir=pasta_modelos, compute_type=precisao_local,
                                 threads=threads_locais, device=dispositivo_local,
                                 model_name=modelo_local, quantization=quantizacao_modelo,
                                 beam_size=feixe, batch_size=lote_modelo,
                                 portuguese_variant=variante_portugues,
                                 terminology_profile=perfil_terminologico,
                                 custom_glossary=glossario_personalizado,
                                 protect_elements=proteger_elementos)
    result = translator.translate(texto)
    if _is_mixed_source(source):
        print(f"Idioma do trecho: {translator.last_source}")
    print("Motor utilizado: " + " + ".join(translator.last_providers))
    return result


def translate_piece(translator, text, context=None):
    # A única camada de retentativas está no cliente. Nunca duplica as tentativas.
    return translator.translate(text)


def translate_text_uncached(translator, text, delay_between_requests=0, context=None):
    return " ".join(translate_piece(translator, part, context) for part in split_text(text)).strip()


def translate_text(translator, text, cache, cache_path, source_lang, target_lang, context=None):
    return translator.translate_cached(text, cache, cache_path)


def translate_units_fast(units, cache, cache_path, source_lang, target_lang, workers=1,
                         page_number=None, engine="auto", timeout=25):
    """Compatibilidade: o modo antigo usa agora a mesma fila sequencial protegida."""
    translator = HybridTranslator(source_lang, target_lang, engine, timeout)
    results = []
    for unit in units:
        results.append(translate_text(translator, normalize_spaces(unit["text"]), cache,
                                      cache_path, source_lang, target_lang))
    return results, {}


# ============================================================
# ANOTAÇÕES PDF
# ============================================================
def add_translation_comment(page, unit, translated_text: str, source_lang: str, target_lang: str, motor=None):
    """Adiciona tradução válida com realce claro e discreto."""
    subject = (
        f"Tradução {source_lang.upper()} → {target_lang.upper()}"
        if source_lang != "auto"
        else f"Tradução automática → {target_lang.upper()}"
    )
    if motor:
        subject += f" | {motor}"
    annot = page.add_highlight_annot(unit["quads"])
    annot.set_colors(stroke=TRANSLATED_HIGHLIGHT_COLOR)
    annot.set_info(
        content=translated_text,
        title=COMMENT_AUTHOR,
        subject=subject,
    )
    annot.update(opacity=TRANSLATED_HIGHLIGHT_OPACITY)

    if ADD_STICKY_NOTE:
        r = unit["rect"]
        x = min(page.rect.x1 - 14, r.x1 + 3)
        y = min(page.rect.y1 - 14, max(page.rect.y0 + 3, r.y0))
        note = page.add_text_annot(fitz.Point(x, y), translated_text, icon=STICKY_NOTE_ICON)
        note.set_info(
            content=translated_text,
            title=COMMENT_AUTHOR,
            subject=subject,
        )
        note.update()


def add_failed_translation_comment(page, unit, error_message: str | None = None):
    """Marca em vermelho um trecho que permaneceu sem tradução.

    A mensagem técnica do serviço não é colocada no comentário. Ela continua
    disponível apenas no log e no arquivo JSON de pendências.
    """
    annot = page.add_highlight_annot(unit["quads"])
    annot.set_colors(stroke=FAILED_HIGHLIGHT_COLOR)
    annot.set_info(
        content=FAILED_COMMENT_TEXT,
        title=COMMENT_AUTHOR,
        subject="Tradução pendente",
    )
    annot.update(opacity=FAILED_HIGHLIGHT_OPACITY)

    if ADD_STICKY_NOTE:
        r = unit["rect"]
        x = min(page.rect.x1 - 14, r.x1 + 3)
        y = min(page.rect.y1 - 14, max(page.rect.y0 + 3, r.y0))
        note = page.add_text_annot(
            fitz.Point(x, y),
            FAILED_COMMENT_TEXT,
            icon=STICKY_NOTE_ICON,
        )
        try:
            note.set_colors(stroke=FAILED_HIGHLIGHT_COLOR)
        except Exception:
            pass
        note.set_info(
            content=FAILED_COMMENT_TEXT,
            title=COMMENT_AUTHOR,
            subject="Tradução pendente",
        )
        note.update()



# ============================================================
# EXTRAÇÃO DE TEXTO PELO CHROME (OCR NATIVO DO NAVEGADOR)
# ============================================================
# Ideia desta versão:
# 1) o PDF é servido apenas em http://127.0.0.1, simulando o acesso web;
# 2) uma instância ISOLADA do Chrome é aberta com acessibilidade habilitada;
# 3) o próprio chrome://accessibility/ fornece a árvore que contém o OCR;
# 4) o Python recupera os parágrafos e, quando o Chrome expõe bounds,
#    converte-os em coordenadas do PDF para manter highlights/comentários.
#
# Nada é instalado globalmente. A única dependência adicional, websocket-client,
# se necessária, é instalada em .tradutor_chrome_deps ao lado deste arquivo.


def _normalizar_motor_texto(value):
    v = str(value or "auto").strip().lower()
    aliases = {
        "auto": "auto", "automatico": "auto", "automático": "auto",
        "nativo": "nativo", "native": "nativo", "pymupdf": "nativo",
        "chrome": "chrome", "ocr": "chrome", "chrome_ocr": "chrome",
    }
    if v not in aliases:
        raise ValueError("motor_texto deve ser 'auto', 'nativo' ou 'chrome'.")
    return aliases[v]


def _find_chrome_executable(explicit=None):
    """Localiza Chrome; se não houver, tenta Edge/Chromium como fallback."""
    if explicit:
        p = Path(explicit).expanduser()
        if p.exists():
            return p
        raise FileNotFoundError(f"Executável do navegador não encontrado: {p}")

    candidates = []
    # PATH
    for name in ("chrome", "chrome.exe", "google-chrome", "google-chrome-stable", "chromium", "chromium.exe", "msedge", "msedge.exe"):
        found = shutil.which(name)
        if found:
            candidates.append(Path(found))

    # Windows: locais usuais
    env = os.environ
    for root in (env.get("PROGRAMFILES"), env.get("PROGRAMFILES(X86)"), env.get("LOCALAPPDATA")):
        if not root:
            continue
        rootp = Path(root)
        candidates.extend([
            rootp / "Google" / "Chrome" / "Application" / "chrome.exe",
            rootp / "Microsoft" / "Edge" / "Application" / "msedge.exe",
            rootp / "Chromium" / "Application" / "chrome.exe",
        ])

    seen = set()
    for p in candidates:
        try:
            rp = p.resolve()
        except Exception:
            rp = p
        if str(rp).lower() in seen:
            continue
        seen.add(str(rp).lower())
        if p.exists():
            return p

    raise FileNotFoundError(
        "Chrome/Chromium/Edge não foi localizado. Informe chrome_exe=r'C:\\\\...\\\\chrome.exe'."
    )


def _ensure_websocket_client(auto_install=True):
    """Importa websocket-client; se preciso, instala-o SOMENTE em pasta local."""
    try:
        import websocket  # type: ignore
        if hasattr(websocket, "create_connection"):
            return websocket
    except Exception:
        pass

    base = Path(__file__).resolve().parent if "__file__" in globals() else Path.cwd()
    deps_dir = base / CHROME_LOCAL_DEPS_DIRNAME
    deps_dir.mkdir(parents=True, exist_ok=True)
    if str(deps_dir) not in sys.path:
        sys.path.insert(0, str(deps_dir))

    try:
        import websocket  # type: ignore
        if hasattr(websocket, "create_connection"):
            return websocket
    except Exception:
        pass

    if not auto_install:
        raise RuntimeError(
            "O modo Chrome precisa de 'websocket-client'. Instale com pip ou use "
            "instalar_dependencia_chrome=True para instalação local automática."
        )

    print(f"Chrome OCR: preparando dependência local em {deps_dir}")
    cmd = [
        sys.executable, "-m", "pip", "install",
        "--disable-pip-version-check", "--no-input",
        "--target", str(deps_dir), "websocket-client>=1.8,<2",
    ]
    subprocess.check_call(cmd)

    # O import pode ter uma entrada inválida anterior no sys.modules.
    sys.modules.pop("websocket", None)
    import websocket  # type: ignore
    if not hasattr(websocket, "create_connection"):
        raise RuntimeError("A instalação local de websocket-client não ficou utilizável.")
    return websocket


class _QuietPDFHandler(http.server.SimpleHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass


def _start_local_pdf_server(pdf_path: Path):
    """Serve somente a pasta do PDF em localhost; não expõe nada para a rede."""
    handler = functools.partial(_QuietPDFHandler, directory=str(pdf_path.parent))
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler)
    thread = _threading.Thread(target=server.serve_forever, daemon=True, name="pdf_local_http")
    thread.start()
    filename = _urlparse.quote(pdf_path.name)
    url = f"http://127.0.0.1:{server.server_address[1]}/{filename}"
    return server, url


class _CDPConnection:
    def __init__(self, websocket_module, ws_url, timeout=10):
        self.ws = websocket_module.create_connection(
            ws_url,
            timeout=timeout,
            origin="http://localhost",
        )
        self._id = 0

    def call(self, method, params=None):
        self._id += 1
        rid = self._id
        self.ws.send(json.dumps({"id": rid, "method": method, "params": params or {}}))
        while True:
            msg = json.loads(self.ws.recv())
            if msg.get("id") != rid:
                continue
            if "error" in msg:
                raise RuntimeError(f"CDP {method}: {msg['error']}")
            return msg.get("result", {})

    def eval(self, expression):
        result = self.call(
            "Runtime.evaluate",
            {"expression": expression, "returnByValue": True, "awaitPromise": True},
        )
        return result.get("result", {}).get("value")

    def close(self):
        try:
            self.ws.close()
        except Exception:
            pass


def _wait_devtools_port(profile_dir: Path, proc, timeout=20):
    port_file = profile_dir / "DevToolsActivePort"
    deadline = time.time() + timeout
    while time.time() < deadline:
        if port_file.exists():
            lines = port_file.read_text(encoding="utf-8", errors="ignore").splitlines()
            if lines:
                return int(lines[0])
        if proc.poll() is not None:
            raise RuntimeError("O navegador foi encerrado antes de disponibilizar a depuração remota.")
        time.sleep(0.15)
    raise TimeoutError("Chrome não disponibilizou a porta de depuração no tempo esperado.")


def _devtools_json(port, path="/json/list", timeout=5, method=None):
    req = _urlrequest.Request(f"http://127.0.0.1:{port}{path}", method=method or "GET")
    with _urlrequest.urlopen(req, timeout=timeout) as response:
        return json.loads(response.read().decode("utf-8"))


def _create_devtools_target(port, url):
    encoded = _urlparse.quote(url, safe=":/?=&%#")
    # Chrome recente exige PUT em /json/new.
    try:
        return _devtools_json(port, f"/json/new?{encoded}", method="PUT")
    except Exception:
        return _devtools_json(port, f"/json/new?{encoded}")


def _wait_for_accessibility_page(cdp: _CDPConnection, pdf_hint: str, timeout=20):
    deadline = time.time() + timeout
    while time.time() < deadline:
        body = cdp.eval("document.body ? document.body.innerText : ''") or ""
        if "accessibility" in body.lower() and pdf_hint.lower() in body.lower():
            return body
        # Às vezes a lista de páginas demora a aparecer mesmo com a página carregada.
        if pdf_hint.lower() in body.lower():
            return body
        time.sleep(0.4)
    return cdp.eval("document.body ? document.body.innerText : ''") or ""


def _click_internal_and_show_tree(cdp: _CDPConnection, pdf_hint: str):
    # Habilita o formato interno: é nele que aparecem pdfRoot/region/paragraph/staticText.
    cdp.eval("""
        (() => {
            const x = document.getElementById('internal');
            if (x && !x.checked) x.click();
            return !!x;
        })()
    """)
    time.sleep(0.35)

    hint_js = json.dumps(pdf_hint.lower())
    script = f"""
        (() => {{
            const hint = {hint_js};
            const rows = Array.from(document.querySelectorAll('#pages .row'));
            const row = rows.find(r => (r.innerText || '').toLowerCase().includes(hint));
            if (!row) return {{ok:false, reason:'row-not-found', rows:rows.map(r=>r.innerText)}};
            const buttons = Array.from(row.querySelectorAll('button'));
            const button = buttons.find(b => /show|refresh/i.test(b.innerText || '') || /showTree|showOrRefreshTree/.test(b.id || ''));
            if (!button) return {{ok:false, reason:'button-not-found', row:row.innerText}};
            button.click();
            return {{ok:true, rowId:row.id, buttonId:button.id, rowText:row.innerText}};
        }})()
    """
    return cdp.eval(script)


def _read_accessibility_tree(cdp: _CDPConnection, pdf_hint: str):
    hint_js = json.dumps(pdf_hint.lower())
    script = f"""
        (() => {{
            const hint = {hint_js};
            const rows = Array.from(document.querySelectorAll('#pages .row'));
            const row = rows.find(r => (r.innerText || '').toLowerCase().includes(hint));
            if (!row) return '';
            const pre = row.querySelector('pre');
            return pre ? (pre.textContent || '') : '';
        }})()
    """
    return cdp.eval(script) or ""


def _refresh_accessibility_tree(cdp: _CDPConnection, pdf_hint: str):
    hint_js = json.dumps(pdf_hint.lower())
    script = f"""
        (() => {{
            const hint = {hint_js};
            const rows = Array.from(document.querySelectorAll('#pages .row'));
            const row = rows.find(r => (r.innerText || '').toLowerCase().includes(hint));
            if (!row) return false;
            const buttons = Array.from(row.querySelectorAll('button'));
            const button = buttons.find(b => /refresh/i.test(b.innerText || '') || /showTree|showOrRefreshTree/.test(b.id || ''));
            if (!button) return false;
            button.click();
            return true;
        }})()
    """
    return bool(cdp.eval(script))


def _unescape_ax_name(s: str) -> str:
    # O dump normalmente escapa apóstrofos/backslashes. Não usamos unicode_escape
    # para não corromper acentos UTF-8 já corretos.
    return s.replace("\\'", "'").replace('\\"', '"').replace("\\\\", "\\")


def _extract_ax_name(line: str):
    # Formato atual: staticText name='texto' ...
    m = re.search(r"\bname='((?:\\.|[^'])*)'", line)
    if m:
        return _unescape_ax_name(m.group(1))
    # Formato usado em alguns dumps/testes: staticText 'texto'
    m = re.search(r"\b(?:staticText|heading|link)\s+'((?:\\.|[^'])*)'", line, re.I)
    if m:
        return _unescape_ax_name(m.group(1))
    return ""


def _extract_ax_bounds(line: str):
    """Retorna (x,y,w,h) quando o dump do Chrome expõe geometria."""
    patterns = [
        r"location=\((-?\d+(?:\.\d+)?),\s*(-?\d+(?:\.\d+)?)\)\s+size=\((\d+(?:\.\d+)?),\s*(\d+(?:\.\d+)?)\)",
        r"bounds=\((-?\d+(?:\.\d+)?),\s*(-?\d+(?:\.\d+)?),\s*(\d+(?:\.\d+)?),\s*(\d+(?:\.\d+)?)\)",
    ]
    for pat in patterns:
        m = re.search(pat, line)
        if m:
            return tuple(float(x) for x in m.groups())
    return None


def _page_number_from_region(line: str):
    if not re.search(r"\bregion\b", line, re.I):
        return None
    name = _extract_ax_name(line)
    if not name:
        # formato curto: region 'Page 1'
        m = re.search(r"\bregion\s+'((?:\\.|[^'])*)'", line, re.I)
        name = _unescape_ax_name(m.group(1)) if m else ""
    m = re.search(r"(?:page|p[aá]gina|pagina|seite)\s*(\d+)", name, re.I)
    return int(m.group(1)) if m else None


def _parse_chrome_accessibility_tree(tree_text: str):
    """
    Converte o dump do chrome://accessibility/ em:
      {pagina: {'page_bounds': (x,y,w,h)|None,
                'units': [{'text':..., 'bounds':..., 'line_bounds': [...]}]}}
    """
    pages = {}
    current_page = None
    current = None

    def flush():
        nonlocal current
        if current_page is None or current is None:
            current = None
            return
        text = normalize_spaces(current.get("text", ""))
        if text and not is_machine_noise(text):
            low = text.lower()
            if not any(marker in low for marker in (
                "start of extracted text", "end of extracted text",
                "início do texto extraído", "fim do texto extraído",
                "powered by google ai", "texto extraído, desenvolvido pelo google",
            )):
                current["text"] = text
                pages.setdefault(current_page, {"page_bounds": None, "units": []})["units"].append(current)
        current = None

    for raw in tree_text.splitlines():
        line = raw.strip()
        if not line:
            continue

        pno = _page_number_from_region(line)
        if pno is not None:
            flush()
            current_page = pno
            pages.setdefault(pno, {"page_bounds": None, "units": []})
            b = _extract_ax_bounds(line)
            if b:
                pages[pno]["page_bounds"] = b
            continue

        if current_page is None:
            continue

        # Um paragraph/heading marca uma nova unidade lógica.
        if re.search(r"\b(?:paragraph|heading)\b", line, re.I) and not re.search(r"\b(?:staticText|inlineTextBox)\b", line, re.I):
            flush()
            current = {"text": "", "bounds": _extract_ax_bounds(line), "line_bounds": []}
            continue

        if re.search(r"\bstaticText\b", line, re.I):
            text = _extract_ax_name(line)
            if not text:
                continue
            low_text = normalize_spaces(text).lower()
            if any(marker == low_text for marker in (
                "start of extracted text", "end of extracted text",
                "início do texto extraído", "fim do texto extraído",
            )):
                continue
            if current is None:
                current = {"text": "", "bounds": None, "line_bounds": []}
            # Em geral há um staticText por parágrafo. Se houver vários, junta-os.
            if current["text"]:
                current["text"] = merge_text(current["text"], text)
            else:
                current["text"] = text
            b = _extract_ax_bounds(line)
            if b and current.get("bounds") is None:
                current["bounds"] = b
            continue

        if re.search(r"\binlineTextBox\b", line, re.I):
            if current is not None:
                b = _extract_ax_bounds(line)
                if b:
                    current["line_bounds"].append(b)
            continue

    flush()
    return pages


def _alpha_count_units(page_data):
    if not page_data:
        return 0
    return sum(len(re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ]", u.get("text", ""))) for u in page_data.get("units", []))


def _chrome_cache_path(pdf_path: Path):
    return pdf_path.with_name(f"{pdf_path.stem}_chrome_ocr_cache.json")


def _pdf_sha256(path: Path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _load_chrome_ocr_cache(pdf_path: Path, requested_pages):
    path = _chrome_cache_path(pdf_path)
    if not path.exists():
        return None
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
        if obj.get("pdf_sha256") != _pdf_sha256(pdf_path):
            return None
        pages = {int(k): v for k, v in obj.get("pages", {}).items()}
        if all(p in pages and _alpha_count_units(pages[p]) >= CHROME_MIN_ALPHA_PER_PAGE for p in requested_pages):
            return pages
    except Exception:
        return None
    return None


def _save_chrome_ocr_cache(pdf_path: Path, pages):
    path = _chrome_cache_path(pdf_path)
    payload = {
        "pdf_sha256": _pdf_sha256(pdf_path),
        "pages": {str(k): v for k, v in pages.items()},
    }
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    return path




def _prepare_isolated_chrome_profile(profile_dir: Path):
    """Ativa OCR de PDF no perfil isolado sem alterar o perfil normal do Chrome."""
    default_dir = profile_dir / "Default"
    default_dir.mkdir(parents=True, exist_ok=True)
    pref_path = default_dir / "Preferences"
    try:
        prefs = json.loads(pref_path.read_text(encoding="utf-8")) if pref_path.exists() else {}
    except Exception:
        prefs = {}

    settings = prefs.setdefault("settings", {})
    a11y = settings.setdefault("a11y", {})
    a11y["pdf_ocr_always_active"] = True

    # Ajuda o ScreenAI / OCR a priorizar idiomas plausíveis sem limitar o reconhecimento.
    intl = prefs.setdefault("intl", {})
    intl.setdefault("accept_languages", "fr,en-US,en,pt-BR,pt,es")

    pref_path.write_text(json.dumps(prefs, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
    return pref_path


def _ax_value(obj):
    if isinstance(obj, dict):
        return obj.get("value", "")
    return obj or ""


def _ax_role(node):
    return str(_ax_value(node.get("role"))).strip()


def _ax_name(node):
    return normalize_spaces(str(_ax_value(node.get("name"))))


def _page_no_from_ax_node(node):
    role = _ax_role(node).lower()
    if role not in {"region", "group", "genericcontainer", "section"}:
        return None
    name = _ax_name(node)
    m = re.search(r"(?:page|p[aá]gina|pagina|seite)\s*(\d+)", name, re.I)
    return int(m.group(1)) if m else None


def _collect_descendant_ids(node_id, by_id, *, limit=25000):
    out = []
    stack = list(reversed(by_id.get(node_id, {}).get("childIds", []) or []))
    seen = set()
    while stack and len(out) < limit:
        nid = stack.pop()
        if nid in seen:
            continue
        seen.add(nid)
        out.append(nid)
        children = by_id.get(nid, {}).get("childIds", []) or []
        stack.extend(reversed(children))
    return out


def _units_from_ax_page(page_node, by_id):
    """Extrai unidades textuais do AX tree evitando duplicar paragraph/staticText."""
    descendants = _collect_descendant_ids(page_node.get("nodeId"), by_id)
    paragraph_ids = []
    for nid in descendants:
        role = _ax_role(by_id.get(nid, {})).lower()
        if role in {"paragraph", "heading", "listitem", "blockquote"}:
            paragraph_ids.append(nid)

    units = []
    used_static = set()
    for pid in paragraph_ids:
        texts = []
        for nid in [pid] + _collect_descendant_ids(pid, by_id, limit=5000):
            n = by_id.get(nid, {})
            role = _ax_role(n).lower()
            if role in {"statictext", "inlinetextbox"}:
                t = _ax_name(n)
                if t and nid not in used_static:
                    texts.append(t)
                    used_static.add(nid)
        text = normalize_spaces(" ".join(texts))
        if text and not is_machine_noise(text):
            units.append({"text": text, "bounds": None, "line_bounds": []})

    # Fallback: há versões do viewer em que não aparecem nós paragraph.
    leftovers = []
    for nid in descendants:
        n = by_id.get(nid, {})
        role = _ax_role(n).lower()
        if role == "statictext" and nid not in used_static:
            t = _ax_name(n)
            if t and not is_machine_noise(t):
                leftovers.append(t)
    if leftovers:
        # Agrupa em blocos moderados para não criar uma anotação por linha.
        buf = []
        chars = 0
        for t in leftovers:
            if buf and (chars + len(t) > 900 or re.search(r"[.!?;:]$", buf[-1])):
                text = normalize_spaces(" ".join(buf))
                if text:
                    units.append({"text": text, "bounds": None, "line_bounds": []})
                buf, chars = [], 0
            buf.append(t)
            chars += len(t) + 1
        if buf:
            text = normalize_spaces(" ".join(buf))
            if text:
                units.append({"text": text, "bounds": None, "line_bounds": []})

    # Remove duplicatas mantendo ordem.
    dedup = []
    seen_text = set()
    for u in units:
        key = normalize_spaces(u["text"])
        if key and key not in seen_text:
            seen_text.add(key)
            dedup.append(u)
    return dedup


def _parse_cdp_ax_nodes(nodes):
    """Converte Accessibility.getFullAXTree em estrutura por página."""
    by_id = {n.get("nodeId"): n for n in nodes if n.get("nodeId") is not None}
    pages = {}
    for node in nodes:
        pno = _page_no_from_ax_node(node)
        if pno is None:
            continue
        units = _units_from_ax_page(node, by_id)
        if units:
            pages[pno] = {"page_bounds": None, "units": units}

    # Fallback para uma árvore sem regiões de página: útil no teste da página 1.
    if not pages:
        texts = []
        for n in nodes:
            if _ax_role(n).lower() == "statictext":
                t = _ax_name(n)
                if t and not is_machine_noise(t):
                    texts.append(t)
        if texts:
            joined = normalize_spaces(" ".join(texts))
            if joined:
                pages[1] = {"page_bounds": None, "units": [{"text": joined, "bounds": None, "line_bounds": []}]}
    return pages


def _frame_ids_from_tree(frame_tree):
    ids = []
    def walk(item):
        if not isinstance(item, dict):
            return
        frame = item.get("frame") or {}
        fid = frame.get("id")
        if fid:
            ids.append(fid)
        for child in item.get("childFrames", []) or []:
            walk(child)
    walk(frame_tree or {})
    return ids


def _merge_page_data(dst, src):
    for pno, pdata in (src or {}).items():
        entry = dst.setdefault(int(pno), {"page_bounds": pdata.get("page_bounds"), "units": []})
        known = {normalize_spaces(u.get("text", "")) for u in entry.get("units", [])}
        for u in pdata.get("units", []) or []:
            txt = normalize_spaces(u.get("text", ""))
            if txt and txt not in known:
                entry["units"].append(u)
                known.add(txt)
    return dst


def _direct_ax_from_target(websocket_module, target, timeout=15):
    """Lê o AX tree diretamente do target do PDF, sem usar chrome://accessibility/."""
    ws_url = target.get("webSocketDebuggerUrl")
    if not ws_url:
        return {}
    cdp = None
    try:
        cdp = _CDPConnection(websocket_module, ws_url, timeout=timeout)
        try:
            cdp.call("Page.enable")
        except Exception:
            pass
        cdp.call("Accessibility.enable")

        frame_ids = [None]
        try:
            ft = cdp.call("Page.getFrameTree").get("frameTree", {})
            frame_ids.extend(_frame_ids_from_tree(ft))
        except Exception:
            pass

        merged = {}
        seen_frames = set()
        for fid in frame_ids:
            key = fid or "__root__"
            if key in seen_frames:
                continue
            seen_frames.add(key)
            try:
                params = {"frameId": fid} if fid else {}
                nodes = cdp.call("Accessibility.getFullAXTree", params).get("nodes", [])
                _merge_page_data(merged, _parse_cdp_ax_nodes(nodes))
            except Exception:
                continue
        return merged
    finally:
        if cdp is not None:
            cdp.close()


def _choose_pdf_targets(targets, pdf_hint, pdf_url):
    scored = []
    hint = (pdf_hint or "").lower()
    url_low = (pdf_url or "").lower()
    for t in targets:
        if t.get("type") not in {"page", "iframe", "webview"}:
            continue
        hay = (str(t.get("title", "")) + " " + str(t.get("url", ""))).lower()
        score = 0
        if hint and hint in hay:
            score += 10
        if url_low and (url_low in hay or hay in url_low):
            score += 8
        if "pdf" in hay:
            score += 2
        if "mhjfbmdgcfjbbpaeojofohoefgiehjai" in hay:
            score += 5
        if score:
            scored.append((score, t))
    scored.sort(key=lambda x: x[0], reverse=True)
    return [t for _, t in scored]

def extrair_texto_com_chrome(
    pdf_path,
    *,
    paginas=None,
    chrome_exe=None,
    timeout=CHROME_OCR_TIMEOUT_SECONDS,
    poll=CHROME_OCR_POLL_SECONDS,
    instalar_dependencia=True,
    reusar_cache=True,
    salvar_cache=True,
    url_chrome=None,
    chrome_visivel=True,
):
    """
    Usa o OCR/Searchify do Chrome em perfil isolado.

    v6.1: primeiro consulta diretamente o Accessibility.getFullAXTree do target
    do PDF. O chrome://accessibility/ fica apenas como fallback. O perfil isolado
    recebe a preferência de OCR de PDF, e PdfSearchify/PdfSearchifySave são
    habilitados somente para essa instância do navegador.
    """
    pdf_path = Path(pdf_path).resolve()
    if not pdf_path.exists():
        raise FileNotFoundError(pdf_path)

    with fitz.open(pdf_path) as d:
        total_pages = len(d)
    requested = sorted(set(int(p) for p in (paginas or range(1, total_pages + 1)) if 1 <= int(p) <= total_pages))
    if not requested:
        return {}

    if reusar_cache:
        cached = _load_chrome_ocr_cache(pdf_path, requested)
        if cached is not None:
            print(f"Chrome OCR: cache reutilizado ({_chrome_cache_path(pdf_path).name})")
            return cached

    websocket = _ensure_websocket_client(auto_install=instalar_dependencia)
    browser = _find_chrome_executable(chrome_exe)
    print(f"Chrome OCR: navegador = {browser}")

    server = None
    proc = None
    profile_base = Path(__file__).resolve().parent if "__file__" in globals() else Path.cwd()
    profile_dir = profile_base / CHROME_LOCAL_PROFILE_DIRNAME
    profile_dir.mkdir(parents=True, exist_ok=True)
    pref_path = _prepare_isolated_chrome_profile(profile_dir)
    print(f"Chrome OCR: perfil isolado com OCR ativado = {pref_path.parent.parent}")

    if url_chrome:
        pdf_url = str(url_chrome)
    else:
        server, pdf_url = _start_local_pdf_server(pdf_path)
        print(f"Chrome OCR: PDF servido localmente em {pdf_url}")

    args = [
        str(browser),
        "--remote-debugging-port=0",
        f"--user-data-dir={profile_dir}",
        "--remote-allow-origins=*",
        "--force-renderer-accessibility=complete",
        "--enable-features=PdfSearchify,PdfSearchifySave",
        "--disable-features=PdfOopif",
        "--no-first-run",
        "--no-default-browser-check",
        "--disable-sync",
        "--lang=fr",
        "--new-window",
    ]
    if not chrome_visivel:
        args.extend(["--headless=new", "--disable-gpu"])
    args.append(pdf_url)

    try:
        port_file = profile_dir / "DevToolsActivePort"
        if port_file.exists():
            try:
                port_file.unlink()
            except Exception:
                pass

        proc = subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        port = _wait_devtools_port(profile_dir, proc, timeout=min(30, float(timeout)))
        print(f"Chrome OCR: depuração conectada na porta {port}")
        print("Chrome OCR: PdfSearchify + PdfSearchifySave ativados somente nesta instância")

        pdf_hint = pdf_path.name
        deadline = time.time() + float(timeout)
        best_pages = {}
        last_score = -1
        stable = 0
        fallback_attempted = False

        while time.time() < deadline:
            if proc.poll() is not None:
                raise RuntimeError("A instância isolada do Chrome foi encerrada durante o OCR.")

            time.sleep(max(0.6, float(poll)))
            try:
                targets = _devtools_json(port)
            except Exception as exc:
                print(f"Chrome OCR: lista de targets indisponível momentaneamente: {exc}")
                continue

            candidates = _choose_pdf_targets(targets, pdf_hint, pdf_url)
            merged_now = {}
            for target in candidates[:5]:
                try:
                    _merge_page_data(merged_now, _direct_ax_from_target(websocket, target, timeout=10))
                except Exception:
                    # O target pode ser recriado enquanto o Searchify trabalha; será reencontrado no próximo ciclo.
                    continue

            score = sum(_alpha_count_units(merged_now.get(p)) for p in requested)
            if score > last_score:
                best_pages = merged_now or best_pages
                last_score = score
                stable = 0
                print(f"Chrome OCR direto: {score} letras úteis reconhecidas nas páginas solicitadas")
            else:
                stable += 1

            ready = all(_alpha_count_units(merged_now.get(p)) >= CHROME_MIN_ALPHA_PER_PAGE for p in requested)
            if ready and stable >= 1:
                best_pages = merged_now
                break

            # Fallback antigo só depois de algum tempo; qualquer queda da conexão é absorvida e não encerra o notebook.
            elapsed = float(timeout) - max(0.0, deadline - time.time())
            if not fallback_attempted and elapsed >= min(25.0, float(timeout) * 0.35):
                fallback_attempted = True
                try:
                    acc_target = _create_devtools_target(port, "chrome://accessibility/")
                    acc_cdp = _CDPConnection(websocket, acc_target["webSocketDebuggerUrl"], timeout=10)
                    try:
                        acc_cdp.call("Runtime.enable")
                        _wait_for_accessibility_page(acc_cdp, pdf_hint, timeout=8)
                        click_result = _click_internal_and_show_tree(acc_cdp, pdf_hint)
                        hint_tree = pdf_hint
                        if isinstance(click_result, dict) and not click_result.get("ok", False):
                            hint_tree = "127.0.0.1" if not url_chrome else pdf_url
                            _click_internal_and_show_tree(acc_cdp, hint_tree)
                        time.sleep(2)
                        tree = _read_accessibility_tree(acc_cdp, hint_tree)
                        parsed = _parse_chrome_accessibility_tree(tree) if tree else {}
                        _merge_page_data(best_pages, parsed)
                        fbscore = sum(_alpha_count_units(best_pages.get(p)) for p in requested)
                        if fbscore > last_score:
                            last_score = fbscore
                            print(f"Chrome OCR fallback: {fbscore} letras úteis reconhecidas")
                    finally:
                        acc_cdp.close()
                except Exception as exc:
                    print(f"Chrome OCR: fallback chrome://accessibility não ficou estável ({type(exc).__name__}); continuando pelo CDP direto.")

        filtered = {p: best_pages[p] for p in requested if p in best_pages and _alpha_count_units(best_pages[p]) > 0}
        if not filtered:
            raise RuntimeError(
                "O Chrome abriu o PDF, mas o perfil isolado ainda não expôs texto OCR ao CDP. "
                "Isso normalmente significa que o componente local ScreenAI/Searchify ainda está sendo preparado. "
                "Deixe a janela aberta por mais tempo e tente novamente, ou use url_chrome com o endereço que já fica selecionável no seu Chrome normal."
            )

        if salvar_cache:
            cache_file = _save_chrome_ocr_cache(pdf_path, best_pages)
            print(f"Chrome OCR: cache salvo em {cache_file.name}")
        return filtered

    finally:
        if proc is not None:
            try:
                proc.terminate()
                proc.wait(timeout=6)
            except Exception:
                try:
                    proc.kill()
                except Exception:
                    pass
        if server is not None:
            try:
                server.shutdown()
                server.server_close()
            except Exception:
                pass

def testar_chrome_ocr(
    nome_pdf,
    paginas=1,
    *,
    chrome_exe=None,
    chrome_timeout=CHROME_OCR_TIMEOUT_SECONDS,
    url_chrome=None,
    chrome_visivel=True,
):
    """Teste isolado: executa apenas a extração OCR do Chrome, sem traduzir."""
    pdf_path = Path(nome_pdf).resolve()
    with fitz.open(pdf_path) as d:
        total = len(d)
    intervalo = _interpretar_paginas(paginas)
    if intervalo is None:
        requested = list(range(1, total + 1))
    else:
        a, b = intervalo
        requested = list(range(max(1, a), min(total, b) + 1))
    result = extrair_texto_com_chrome(
        pdf_path,
        paginas=requested,
        chrome_exe=chrome_exe,
        timeout=chrome_timeout,
        url_chrome=url_chrome,
        chrome_visivel=chrome_visivel,
    )
    print("=" * 60)
    for pno in requested:
        pdata = result.get(pno, {})
        units = pdata.get("units", [])
        print(f"Página {pno}: {len(units)} trecho(s)")
        for i, unit in enumerate(units, 1):
            print(f"  {i:02d}. {unit.get('text','')[:180]}")
    return result


def _chrome_bounds_to_pdf_rect(bounds, page_bounds, page_rect):
    if not bounds or not page_bounds:
        return None
    x, y, w, h = bounds
    px, py, pw, ph = page_bounds
    if pw <= 0 or ph <= 0 or w <= 0 or h <= 0:
        return None
    sx = page_rect.width / pw
    sy = page_rect.height / ph
    r = fitz.Rect(
        page_rect.x0 + (x - px) * sx,
        page_rect.y0 + (y - py) * sy,
        page_rect.x0 + (x + w - px) * sx,
        page_rect.y0 + (y + h - py) * sy,
    )
    r = r & page_rect
    if r.is_empty or r.width < 1 or r.height < 1:
        return None
    return r


def _chrome_unit_to_pdf_unit(chrome_unit, page_data, page):
    page_bounds = page_data.get("page_bounds")
    rects = []
    for b in chrome_unit.get("line_bounds", []) or []:
        r = _chrome_bounds_to_pdf_rect(b, page_bounds, page.rect)
        if r:
            rects.append(r)
    if not rects:
        r = _chrome_bounds_to_pdf_rect(chrome_unit.get("bounds"), page_bounds, page.rect)
        if r:
            rects.append(r)
    if not rects:
        return {"text": chrome_unit["text"], "rect": None, "quads": [], "chrome_ocr": True}

    union = fitz.Rect(rects[0])
    for r in rects[1:]:
        union.include_rect(r)
    quads = [fitz.Quad(r) for r in rects]
    return {"text": chrome_unit["text"], "rect": union, "quads": quads, "chrome_ocr": True}


def add_chrome_translation_comment(page, unit, translated_text, source_lang, target_lang, index=1):
    """Highlight quando há bounds; caso contrário, nota numerada na margem."""
    subject = f"Chrome OCR | tradução {source_lang.upper()} → {target_lang.upper()}"
    quads = unit.get("quads") or []
    if quads:
        annot = page.add_highlight_annot(quads)
        annot.set_colors(stroke=TRANSLATED_HIGHLIGHT_COLOR)
        annot.set_info(content=translated_text, title=COMMENT_AUTHOR, subject=subject)
        annot.update(opacity=TRANSLATED_HIGHLIGHT_OPACITY)
        return "highlight"

    # Sem geometria exposta pelo Chrome: mantém a tradução acessível como nota.
    per_col = 38
    col = (max(1, index) - 1) // per_col
    row = (max(1, index) - 1) % per_col
    x = max(page.rect.x0 + 8, page.rect.x1 - 14 - 16 * col)
    y = min(page.rect.y1 - 12, page.rect.y0 + 18 + row * 20)
    note = page.add_text_annot(fitz.Point(x, y), translated_text, icon=STICKY_NOTE_ICON)
    note.set_info(content=translated_text, title=COMMENT_AUTHOR, subject=subject)
    note.update()
    return "note"


def add_chrome_failed_comment(page, unit, index=1):
    quads = unit.get("quads") or []
    if quads:
        annot = page.add_highlight_annot(quads)
        annot.set_colors(stroke=FAILED_HIGHLIGHT_COLOR)
        annot.set_info(content=FAILED_COMMENT_TEXT, title=COMMENT_AUTHOR, subject="Chrome OCR | tradução pendente")
        annot.update(opacity=FAILED_HIGHLIGHT_OPACITY)
        return
    per_col = 38
    col = (max(1, index) - 1) // per_col
    row = (max(1, index) - 1) % per_col
    x = max(page.rect.x0 + 8, page.rect.x1 - 14 - 16 * col)
    y = min(page.rect.y1 - 12, page.rect.y0 + 18 + row * 20)
    note = page.add_text_annot(fitz.Point(x, y), FAILED_COMMENT_TEXT, icon=STICKY_NOTE_ICON)
    note.set_info(content=FAILED_COMMENT_TEXT, title=COMMENT_AUTHOR, subject="Chrome OCR | tradução pendente")
    note.update()


# ============================================================
# PROCESSAMENTO PRINCIPAL
# ============================================================
def _normalizar_idioma_origem(lang):
    """Normaliza idioma único, detecção global ou uma lista por trecho."""
    if lang is None:
        return "auto"
    if isinstance(lang, (list, tuple, set)):
        values = sorted(lang) if isinstance(lang, set) else lang
        codes = tuple(dict.fromkeys(str(code).strip().lower() for code in values))
        if not codes or any(not re.fullmatch(r"[a-z]{2,5}", code) for code in codes):
            raise ValueError("Use códigos como ['fr', 'en', 'it', 'pt'] em idioma_origem.")
        return codes
    lang = str(lang).strip().lower()
    aliases_auto = {"", "auto", "automatico", "automático", "detect", "detectar"}
    aliases_misto = {"misto", "mixed", "multilingue", "multilíngue", "fr_en", "fr+en"}
    if lang in aliases_auto:
        return "auto"
    if lang in aliases_misto:
        return DEFAULT_MIXED_LANGUAGES
    if "," in lang:
        return _normalizar_idioma_origem(lang.split(","))
    return lang


def _is_mixed_source(source):
    return isinstance(source, tuple)


def _source_display(source):
    return "misto[" + ",".join(source) + "]" if _is_mixed_source(source) else source


def _nome_saida_automatico(input_path: Path, target_lang: str) -> Path:
    return input_path.with_name(f"{input_path.stem}_traduzido_{target_lang}{input_path.suffix}")


def pdf_ja_tem_traducao(path):
    """Detecta comentários criados por este tradutor sem alterar o arquivo."""
    try:
        with fitz.open(path) as doc:
            if doc.needs_pass:
                return False
            for page in doc:
                annotation = page.first_annot
                while annotation:
                    info = annotation.info or {}
                    title = str(info.get("title", "")).casefold()
                    subject = str(info.get("subject", "")).casefold()
                    if "tradução automática" in title or subject.startswith("tradução "):
                        return True
                    annotation = annotation.next
    except (OSError, RuntimeError, ValueError):
        return False
    return False


def _interpretar_paginas(paginas):
    """Aceita None, um inteiro, (início, fim) ou strings como '10-20' / '10:20'."""
    if paginas is None:
        return None

    if isinstance(paginas, int):
        if paginas < 1:
            raise ValueError("O número da página deve ser >= 1.")
        return paginas, paginas

    if isinstance(paginas, (tuple, list)) and len(paginas) == 2:
        inicio, fim = paginas
        inicio = int(inicio)
        fim = int(fim)
        if inicio < 1 or fim < inicio:
            raise ValueError("Intervalo de páginas inválido.")
        return inicio, fim

    if isinstance(paginas, str):
        texto = paginas.strip().lower().replace("páginas", "").replace("paginas", "")
        texto = texto.replace("página", "").replace("pagina", "").replace("pg.", "").replace("pg", "")
        texto = texto.strip()

        # Uma única página: '10'
        if re.fullmatch(r"\d+", texto):
            n = int(texto)
            if n < 1:
                raise ValueError("O número da página deve ser >= 1.")
            return n, n

        # Intervalos: '10-20', '10:20', '10 a 20', '10 até 20'
        m = re.fullmatch(r"(\d+)\s*(?:-|:|a|até|ate)\s*(\d+)", texto)
        if m:
            inicio, fim = map(int, m.groups())
            if inicio < 1 or fim < inicio:
                raise ValueError("Intervalo de páginas inválido.")
            return inicio, fim

    raise ValueError(
        "Use paginas como inteiro, (inicio, fim) ou texto, por exemplo: "
        "paginas=10, paginas=(10, 20) ou paginas='10-20'."
    )


_RUN_LOCK = threading.Lock()


def _exclusive_run(function):
    @functools.wraps(function)
    def wrapped(*args, **kwargs):
        if not _RUN_LOCK.acquire(blocking=False):
            raise RuntimeError("Já existe uma tradução ativa neste módulo. Interrompa-a antes de iniciar outra.")
        try:
            return function(*args, **kwargs)
        finally:
            _RUN_LOCK.release()
    return wrapped


def _save_pdf_atomic(doc, output):
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=output.stem + "_", suffix=".pdf", dir=output.parent)
    os.close(fd)
    try:
        doc.save(temporary, garbage=3, deflate=True, encryption=fitz.PDF_ENCRYPT_KEEP)
        try:
            os.replace(temporary, output)
        except PermissionError as exc:
            # O visualizador do Windows pode manter o PDF final aberto.
            recovered = temporary
            temporary = None
            raise PermissionError(f"Feche {output.name} no leitor de PDF. O resultado foi salvo em {recovered}.") from exc
    finally:
        if temporary and os.path.exists(temporary):
            os.unlink(temporary)


@_exclusive_run
def traduzir_pdf(
    nome_pdf,
    idioma_origem="auto",
    idioma_destino="pt",
    saida=None,
    *,
    paginas=None,
    pagina_inicial=1,
    pagina_final=None,
    adicionar_nota=False,
    modo="seguro",
    trabalhadores=1,
    pausa_min=3.0,
    pausa_max=3.0,
    motor_traducao="local",
    timeout_traducao=25,
    motor_texto="nativo",
    chrome_exe=None,
    chrome_timeout=CHROME_OCR_TIMEOUT_SECONDS,
    chrome_poll=CHROME_OCR_POLL_SECONDS,
    instalar_dependencia_chrome=True,
    reusar_ocr_chrome=True,
    salvar_ocr_chrome=True,
    url_chrome=None,
    chrome_visivel=True,
    intervalo_requisicoes=3.0,
    pausa_429=900,
    pasta_controle=None,
    tentativas_traducao=1,
    espera_maxima=60,
    pasta_modelos=None,
    precisao_local="float16",
    threads_locais=4,
    dispositivo_local="auto",
    modelo_local="nllb_1_3b",
    quantizacao_modelo="float16",
    feixe=None,
    lote_modelo=None,
    variante_portugues="pt-BR",
    perfil_terminologico=None,
    glossario_personalizado=None,
    proteger_elementos=True,
    traduzir_referencias=False,
    unir_blocos_contiguos=True,
    unir_entre_paginas=True,
    gerar_auditoria=True,
    max_caracteres_trecho=MAX_CHARS_PER_UNIT,
    ao_erro_traducao="continuar",
    salvar_a_cada=1,
    senha=None,
    retornar_relatorio=False,
):
    """Traduz um PDF localmente e adiciona a tradução como comentário.

    Esta função sustenta ``traduzir_pasta``. O modelo deve ser preparado antes;
    durante a tradução não há downloads nem chamadas a serviços externos.
    Idiomas mistos são classificados trecho a trecho, e o português já existente
    é preservado. Em falhas, o original é marcado e a execução pode continuar.
    """
    global ADD_STICKY_NOTE
    source = _normalizar_idioma_origem(idioma_origem)
    target = str(idioma_destino).strip().lower()
    if not target or target == "auto":
        raise ValueError("Informe o idioma de destino, por exemplo 'pt'.")
    engine = _translation_mode(motor_traducao)
    text_engine = _normalizar_motor_texto(motor_texto)
    mode = str(modo).strip().lower()
    if mode not in {"normal", "padrao", "padrão", "seguro", "safe", "calmo", "cauteloso",
                    "rapido", "rápido", "fast", "turbo"}:
        raise ValueError("modo deve ser 'normal', 'seguro' ou 'rapido'.")
    interval = _finite_number(intervalo_requisicoes, "intervalo_requisicoes", minimum=1)
    pmin = _finite_number(pausa_min, "pausa_min")
    pmax = _finite_number(pausa_max, "pausa_max")
    if pmax < pmin:
        raise ValueError("Use pausa_max >= pausa_min.")
    if mode in {"seguro", "safe", "calmo", "cauteloso"}:
        interval = max(interval, (pmin + pmax) / 2)
    if not isinstance(salvar_a_cada, int) or salvar_a_cada < 1:
        raise ValueError("salvar_a_cada deve ser inteiro >= 1.")
    try:
        unit_limit = int(max_caracteres_trecho)
    except (TypeError, ValueError) as exc:
        raise ValueError("max_caracteres_trecho deve ser um inteiro >= 200.") from exc
    if unit_limit < 200:
        raise ValueError("max_caracteres_trecho deve ser um inteiro >= 200.")
    error_action = str(ao_erro_traducao).lower().strip().replace("-", "_")
    error_aliases = {"seguir": "continuar", "ignorar": "continuar", "skip": "continuar",
                     "pagina": "pular_pagina", "página": "pular_pagina", "stop": "parar"}
    error_action = error_aliases.get(error_action, error_action)
    if error_action not in {"continuar", "pular_pagina", "parar"}:
        raise ValueError("ao_erro_traducao: 'continuar', 'pular_pagina' ou 'parar'.")
    portuguese_variant = _normalizar_variante_portugues(variante_portugues, target)
    terminology_profile = _normalizar_perfil_terminologico(perfil_terminologico)
    custom_glossary = _normalizar_glossario_personalizado(glossario_personalizado)
    protect_elements = bool(proteger_elementos)
    translate_references = bool(traduzir_referencias)
    merge_contiguous = bool(unir_blocos_contiguos)
    merge_across_pages = bool(unir_entre_paginas)
    create_audit = bool(gerar_auditoria)

    path = Path(nome_pdf).expanduser().resolve()
    if not path.is_file():
        raise FileNotFoundError(f"PDF não encontrado: {path}")
    model_name = _model_name(modelo_local)
    if source == "auto":
        source = _source_from_pdf(path, senha, paginas, pagina_inicial, pagina_final)
    mixed_source = _is_mixed_source(source)
    dominant_source = dominant_score = None
    if mixed_source:
        if target not in source:
            source = tuple([*source, target])
        try:
            dominant_source, dominant_score = _dominant_source_from_pdf(
                path, senha, paginas, pagina_inicial, pagina_final, source)
        except ValueError as exc:
            if "Pouco texto" not in str(exc):
                raise
            dominant_source = next((code for code in source if code != target), target)
            print(f"Aviso: não foi possível estimar o idioma predominante ({exc}); usando {dominant_source}.")
    output = Path(saida).expanduser() if saida else _nome_saida_automatico(path, target)
    if not output.is_absolute():
        output = path.parent / output
    output = output.resolve()
    if output == path or (output.exists() and os.path.samefile(path, output)):
        raise ValueError("O arquivo de saída deve ser diferente do PDF original.")
    output.parent.mkdir(parents=True, exist_ok=True)
    source_label = _source_display(source)
    cache_source = "misto_" + "-".join(source) if mixed_source else source
    cache_path = path.with_name(
        f"{path.stem}_cache_local_{model_name}_{cache_source}_{target}.json"
    )
    report_path = output.with_suffix(".relatorio.json")
    pending_path = output.with_suffix(".pendencias.json")
    audit_path = output.with_suffix(".auditoria.json")
    translator = _criar_tradutor(source, target, engine, timeout_traducao,
                                 interval, pausa_429, pasta_controle,
                                 tentativas_traducao, espera_maxima,
                                 pasta_modelos, precisao_local, threads_locais,
                                 dispositivo_local,
                                 model_name, quantizacao_modelo, feixe, lote_modelo,
                                 portuguese_variant, terminology_profile, custom_glossary,
                                 protect_elements)
    if mixed_source:
        translator.dominant_source = dominant_source
    old_note = ADD_STICKY_NOTE
    ADD_STICKY_NOTE = bool(adicionar_nota)
    doc = None
    try:
        # Protege também o cache do mesmo PDF em outros kernels/processos.
        with _FileLock(str(cache_path) + ".lock", timeout=0):
            cache, _ = sanitize_translation_cache(load_cache(cache_path))
            doc = fitz.open(path)
            if doc.needs_pass and (not senha or not doc.authenticate(senha)):
                raise ValueError("PDF protegido: informe senha='sua senha'.")
            interval_pages = _interpretar_paginas(paginas)
            if interval_pages:
                pagina_inicial, pagina_final = interval_pages
            first = int(pagina_inicial)
            last = min(len(doc), int(pagina_final)) if pagina_final is not None else len(doc)
            if first < 1 or first > last:
                raise ValueError("Intervalo de páginas inválido.")
            numbers = list(range(first, last + 1))
            report = {"versao": __version__, "entrada": str(path), "saida": str(output),
                      "idioma_origem": "misto" if mixed_source else source,
                      "idioma_predominante": dominant_source,
                      "confianca_idioma_predominante": dominant_score,
                      "idiomas_origem": list(source) if mixed_source else [source],
                      "variante_portugues": portuguese_variant,
                      "perfil_terminologico": terminology_profile,
                      "glossario_personalizado": custom_glossary,
                      "proteger_elementos": protect_elements,
                      "traduzir_referencias": translate_references,
                      "unir_blocos_contiguos": merge_contiguous,
                      "unir_entre_paginas": merge_across_pages,
                      "gerar_auditoria": create_audit,
                      "deteccao_idioma": "documento_e_trecho" if mixed_source else "fixo_ou_global",
                      "estado": "em_andamento", "paginas_solicitadas": numbers,
                      "paginas": [], "cache": str(cache_path),
                      "motor_traducao": "local",
                      "modelo_local": model_name,
                      "quantizacao_modelo": quantizacao_modelo,
                      "precisao_execucao": precisao_local,
                      "feixe": feixe or MODELOS_LOCAIS[model_name]["feixe"],
                      "lote_modelo": lote_modelo or MODELOS_LOCAIS[model_name]["lote"],
                      "max_caracteres_trecho": unit_limit,
                      "ao_erro_traducao": error_action,
                      "auditoria": str(audit_path) if create_audit else None,
                      "dispositivo_local_solicitado": dispositivo_local,
                      "rota_local": translator.local.route_label if translator.local else None}

            def save_reports():
                records = [unit for page in report["paginas"] for unit in page["trechos"]]
                audit_records = [
                    {"pagina": unit["pagina"], "trecho": unit["trecho"],
                     "avisos": unit.get("auditoria", []),
                     "original": unit.get("original"), "traducao": unit.get("traducao")}
                    for unit in records if unit.get("auditoria")
                ]
                report["totais"] = {"traduzidos": sum(u["estado"] == "traduzido" for u in records),
                                    "notacoes_preservadas": sum(u["estado"] == "preservado" and
                                        u.get("tipo_preservacao") == "notacao" for u in records),
                                    "idioma_destino_preservados": sum(u["estado"] == "preservado" and
                                        u.get("tipo_preservacao") == "idioma_destino" for u in records),
                                    "referencias_preservadas": sum(u["estado"] == "preservado" and
                                        u.get("tipo_preservacao") == "referencia" for u in records),
                                    "revisao_recomendada": len(audit_records),
                                    "pendentes": sum(u["estado"] not in {"traduzido", "preservado"} for u in records),
                                    **translator.stats,
                                    **(translator.local.recovery_stats if translator.local else {})}
                report["dispositivo_local"] = translator.local.device if translator.local and translator.local.loaded else None
                visited = {page["pagina"] for page in report["paginas"]}
                report["paginas_nao_processadas"] = [p for p in numbers if p not in visited]
                report["atualizado_em"] = datetime.now(timezone.utc).isoformat()
                save_cache(report_path, report)
                save_cache(pending_path, {"estado": report["estado"],
                    "trechos": [u for u in records if u["estado"] not in {"traduzido", "preservado"}],
                    "revisao_recomendada": audit_records,
                    "paginas_sem_texto": [p["pagina"] for p in report["paginas"] if not p["trechos"]],
                    "paginas_nao_processadas": report["paginas_nao_processadas"]})
                if create_audit:
                    save_cache(audit_path, {
                        "versao": __version__, "entrada": str(path), "saida": str(output),
                        "total": len(audit_records), "trechos": audit_records,
                        "atualizado_em": report["atualizado_em"],
                    })

            def checkpoint():
                save_cache(cache_path, cache)
                save_reports()
                _save_pdf_atomic(doc, output)

            print(f"Tradutor v{__version__} | {path.name} | {source_label} → {target}")
            if mixed_source:
                print("Idiomas permitidos por trecho: " + ", ".join(source) + " (detecção local).")
                confidence = f" | confiança {dominant_score:.3f}" if dominant_score is not None else ""
                print(f"Idioma predominante do documento: {dominant_source}{confidence}.")
            print(f"Código carregado: {Path(__file__).resolve()}")
            print(f"Extração: {text_engine} | páginas {first} a {last}")
            print("Modo de tradução: somente local/offline")
            if portuguese_variant == "pt-BR":
                print("Variante de saída: português brasileiro (normalização conservadora)")
            if terminology_profile == "didatica_matematica":
                print("Perfil terminológico: Didática da Matemática")
            if protect_elements:
                print("Proteção: fórmulas, citações, siglas, URLs e dados técnicos")
            if not translate_references:
                print("Bibliografia: preservada no idioma original")
            if create_audit:
                print("Auditoria: trechos suspeitos serão listados separadamente")
            print(f"Falha de tradução: {error_action} | alvo por trecho: {unit_limit} caracteres")
            if translator.local:
                print(f"Modelo local: {translator.local.route_label} | dispositivo solicitado: "
                      f"{dispositivo_local} | {precisao_local}")
                if len(translator.local.route) > 1:
                    print("Aviso: a rota local usa idioma intermediário; revise a terminologia.")
            if mode in {"rapido", "rápido", "fast", "turbo"} or int(trabalhadores) > 1:
                print("Compatibilidade: modo rápido/trabalhadores usa agora a mesma fila sequencial protegida.")
            try:
                repeated = collect_repeated_margin_keys(doc)
                native = {number: extract_blocks(doc[number - 1], repeated) for number in numbers}
                missing = [number for number in numbers if not native[number]]
                chrome_pages = {}
                if missing and text_engine != "nativo":
                    try:
                        chrome_pages = extrair_texto_com_chrome(
                            path, paginas=missing, chrome_exe=chrome_exe, timeout=chrome_timeout,
                            poll=chrome_poll, instalar_dependencia=instalar_dependencia_chrome,
                            reusar_cache=reusar_ocr_chrome, salvar_cache=salvar_ocr_chrome,
                            url_chrome=url_chrome, chrome_visivel=chrome_visivel)
                    except Exception as exc:
                        report["aviso_ocr"] = f"Chrome OCR falhou: {exc}"
                        print(report["aviso_ocr"])

                prepared_pages, units_by_page = {}, {}
                for number in numbers:
                    page = doc[number - 1]
                    blocks = native[number]
                    source_kind = "nativo"
                    if blocks:
                        units = make_logical_units(
                            order_blocks(blocks, page.rect.width), unit_limit,
                            merge_blocks=merge_contiguous,
                        )
                    else:
                        source_kind = "chrome"
                        pdata = chrome_pages.get(number, {})
                        units = [_chrome_unit_to_pdf_unit(u, pdata, page)
                                 for u in pdata.get("units", [])]
                    units = [u for u in units if not is_machine_noise(u["text"])]
                    prepared_pages[number] = (source_kind, units)
                    units_by_page[number] = units

                reference_start = None
                if not translate_references:
                    reference_start = marcar_secao_referencias(units_by_page)
                page_heights = {number: doc[number - 1].rect.height for number in numbers}
                continuations, continuation_groups = ({}, [])
                if merge_across_pages:
                    continuations, continuation_groups = encontrar_continuacoes_entre_paginas(
                        units_by_page, page_heights
                    )
                report["inicio_referencias"] = reference_start
                report["continuacoes_entre_paginas"] = [
                    {"id": group["id"], "paginas": group["paginas"]}
                    for group in continuation_groups
                ]
                continuation_results = {}

                for processed, number in enumerate(numbers, 1):
                    page = doc[number - 1]
                    source_kind, units = prepared_pages[number]
                    page_info = {"pagina": number, "extracao": source_kind if units else "sem_texto", "trechos": []}
                    report["paginas"].append(page_info)
                    for index, unit in enumerate(units, 1):
                        page_info["trechos"].append({"pagina": number, "trecho": index,
                            "original": normalize_spaces(unit["text"]), "traducao": None,
                            "estado": "pendente"})
                    save_reports()
                    print(f"Pág. {number}: {page_info['extracao']} | {len(units)} trechos")
                    if not units:
                        page_info["aviso"] = "Nenhum texto útil extraído. Página não traduzida; verifique o original."
                    for index, (unit, record) in enumerate(zip(units, page_info["trechos"]), 1):
                        if unit.get("preservar_referencia"):
                            record.update(
                                estado="preservado", tipo_preservacao="referencia",
                                motivo="Referência bibliográfica mantida exatamente como no original.",
                            )
                            print(f"   {index:02d}. [Referência preservada] {record['original'][:85]}")
                            continue
                        if is_standalone_math(record["original"]):
                            record.update(estado="preservado", tipo_preservacao="notacao",
                                          motivo="Notação matemática isolada; mantida no original.")
                            print(f"   {index:02d}. [Notação preservada] {record['original'][:85]}")
                            continue

                        member_key = (number, index - 1)
                        continuation = continuations.get(member_key)
                        translation_input = continuation["texto"] if continuation else record["original"]
                        if continuation:
                            record.update(
                                continuacao_entre_paginas=continuation["paginas"],
                                grupo_continuacao=continuation["id"],
                                contexto_traducao=translation_input,
                            )

                        try:
                            stored = continuation_results.get(continuation["id"]) if continuation else None
                            if stored:
                                text = stored["texto"]
                                providers = stored["motores"][:]
                                detected_source = stored["idioma"]
                                source_score = stored["confianca"]
                                source_reason = stored["criterio"]
                            else:
                                text = translate_text(
                                    translator, translation_input, cache, cache_path, source, target
                                )
                                providers = translator.last_providers[:]
                                detected_source = (
                                    getattr(translator, "last_source", None) if mixed_source else source
                                )
                                source_score = (
                                    getattr(translator, "last_source_score", None) if mixed_source else None
                                )
                                source_reason = (
                                    getattr(translator, "last_source_reason", None) if mixed_source else None
                                )
                                if continuation:
                                    continuation_results[continuation["id"]] = {
                                        "texto": text, "motores": providers,
                                        "idioma": detected_source, "confianca": source_score,
                                        "criterio": source_reason,
                                    }
                        except KeyboardInterrupt:
                            record["erro"] = "Execução interrompida pelo usuário."
                            raise
                        except Exception as exc:
                            message = f"{type(exc).__name__}: {exc}"
                            record.update(estado="falhou", erro=message)
                            detected_source = getattr(translator, "last_source", None)
                            if detected_source:
                                record["idioma_detectado"] = detected_source
                                record["confianca_idioma"] = getattr(translator, "last_source_score", None)
                                record["criterio_idioma"] = getattr(translator, "last_source_reason", None)
                            if source_kind == "chrome":
                                add_chrome_failed_comment(page, unit, index)
                            else:
                                add_failed_translation_comment(page, unit, message)
                            print(f"   {index:02d}. [Ignorado] {message}")
                            if error_action == "parar":
                                raise
                            if error_action == "pular_pagina":
                                print(f"   Pulando o restante da página {number}.")
                                for rest_index in range(index, len(units)):
                                    rest_unit = units[rest_index]
                                    rest_record = page_info["trechos"][rest_index]
                                    rest_record.update(estado="pulado", erro="Restante da página pulado após erro de tradução.")
                                    if source_kind == "chrome":
                                        add_chrome_failed_comment(page, rest_unit, rest_index + 1)
                                    else:
                                        add_failed_translation_comment(page, rest_unit, rest_record["erro"])
                                break
                            continue

                        if mixed_source and detected_source == target and providers == ["Original"]:
                            record.update(estado="preservado", tipo_preservacao="idioma_destino",
                                          idioma_detectado=detected_source,
                                          confianca_idioma=source_score,
                                          motivo="Trecho já está no idioma de destino; original preservado.")
                            record["criterio_idioma"] = source_reason
                            print(f"   {index:02d}. [{target.upper()} preservado] {record['original'][:85]}")
                            continue

                        # Falhas ao gravar anotações/PDF não são escondidas como
                        # se fossem erros de tradução.
                        detected_source = detected_source or "fr"
                        comment_text = text
                        if continuation:
                            pages_label = "–".join(map(str, continuation["paginas"]))
                            comment_text = f"[Parágrafo contínuo entre páginas {pages_label}]\n{text}"
                        if source_kind == "chrome":
                            add_chrome_translation_comment(
                                page, unit, comment_text, detected_source, target, index
                            )
                        else:
                            add_translation_comment(
                                page, unit, comment_text, detected_source, target,
                                motor=" + ".join(providers),
                            )
                        record.update(estado="traduzido", traducao=text, motores=providers,
                                      idioma_detectado=detected_source,
                                      confianca_idioma=source_score if mixed_source else None)
                        if mixed_source:
                            record["criterio_idioma"] = source_reason
                        first_continuation_member = (
                            not continuation or continuation["membros"][0] == member_key
                        )
                        if create_audit and first_continuation_member:
                            record["auditoria"] = auditar_traducao(
                                translation_input, text, detected_source
                            )
                        elif continuation:
                            first_page, first_index = continuation["membros"][0]
                            record["auditoria_compartilhada_com"] = {
                                "pagina": first_page, "trecho": first_index + 1
                            }
                        language_label = f"{detected_source} → " if mixed_source else ""
                        audit_label = " | revisar" if record.get("auditoria") else ""
                        print(f"   {index:02d}. [{language_label}{' + '.join(providers)}{audit_label}] {text[:85]}")
                    save_reports()
                    if processed % salvar_a_cada == 0:
                        checkpoint()
                has_pending = any(not p["trechos"] or any(u["estado"] not in {"traduzido", "preservado"}
                                  for u in p["trechos"]) for p in report["paginas"])
                report["estado"] = "concluido_com_pendencias" if has_pending else "concluido"
                checkpoint()
            except KeyboardInterrupt:
                report["estado"] = "interrompido"
                checkpoint()
                print("\nInterrompido. PDF parcial/cache salvos; execute novamente sobre o original para retomar.")
                raise
            except Exception as exc:
                report.update(estado="erro", motivo=f"{type(exc).__name__}: {exc}")
                checkpoint()
                raise
            print(f"Estado: {report['estado']} | {report['totais']['traduzidos']} trechos traduzidos | "
                  f"{report['totais']['notacoes_preservadas']} notações preservadas | "
                  f"{report['totais']['idioma_destino_preservados']} trechos em {target} preservados | "
                  f"{report['totais']['referencias_preservadas']} referências preservadas | "
                  f"{report['totais']['revisao_recomendada']} para revisão | "
                  f"{report['totais']['pendentes']} pendentes | "
                  f"{report['totais']['fragmentos_locais']} fragmentos locais")
            audit_line = f"\nAuditoria: {audit_path}" if create_audit else ""
            print(f"PDF: {output}\nRelatório: {report_path}\nPendências: {pending_path}{audit_line}")
            return report if retornar_relatorio else output
    finally:
        ADD_STICKY_NOTE = old_note
        if doc is not None:
            doc.close()


def traduzir_pasta(
    pasta,
    *,
    pasta_saida=None,
    recursivo=False,
    sobrescrever=False,
    ignorar_ja_traduzidos=True,
    continuar_apos_erro=True,
    salvar_resumo=True,
    **opcoes,
):
    """Traduz sequencialmente todos os PDFs de uma pasta.

    Por padrão, cria a subpasta ``traduzidos``, ignora resultados existentes e
    PDFs que já contenham comentários deste tradutor, e continua após falhas.
    """
    root = Path(pasta).expanduser().resolve()
    if not root.is_dir():
        raise NotADirectoryError(f"Pasta não encontrada: {root}")
    if "saida" in opcoes or "retornar_relatorio" in opcoes:
        raise TypeError("Em traduzir_pasta, use pasta_saida; não informe saida/retornar_relatorio.")

    output_root = Path(pasta_saida).expanduser() if pasta_saida is not None else root / "traduzidos"
    if not output_root.is_absolute():
        output_root = root / output_root
    output_root = output_root.resolve()
    output_root.mkdir(parents=True, exist_ok=True)
    summary_path = output_root / "resumo_traducao.json"

    candidates = root.rglob("*") if recursivo else root.iterdir()
    files = []
    for candidate in candidates:
        if not candidate.is_file() or candidate.suffix.lower() != ".pdf":
            continue
        try:
            candidate.resolve().relative_to(output_root)
            continue
        except ValueError:
            pass
        if re.search(r"_traduzido_[a-z-]+$", candidate.stem, flags=re.IGNORECASE):
            continue
        files.append(candidate.resolve())
    files.sort(key=lambda item: str(item.relative_to(root)).casefold())

    target = str(opcoes.get("idioma_destino", "pt")).strip().lower()
    summary = {
        "versao": __version__,
        "pasta_entrada": str(root),
        "pasta_saida": str(output_root),
        "estado": "em_andamento",
        "arquivos_encontrados": len(files),
        "arquivos": [],
    }

    def save_summary():
        records = summary["arquivos"]
        summary["totais"] = {
            "concluidos": sum(r["estado"] == "concluido" for r in records),
            "com_pendencias": sum(r["estado"] == "concluido_com_pendencias" for r in records),
            "ignorados_existentes": sum(r["estado"] == "ignorado_existente" for r in records),
            "ignorados_ja_traduzidos": sum(r["estado"] == "ignorado_ja_traduzido" for r in records),
            "erros": sum(r["estado"] == "erro" for r in records),
            "trechos_para_revisao": sum(
                int(r.get("totais", {}).get("revisao_recomendada", 0)) for r in records
            ),
        }
        summary["atualizado_em"] = datetime.now(timezone.utc).isoformat()
        if salvar_resumo:
            save_cache(summary_path, summary)

    if not files:
        summary["estado"] = "sem_arquivos"
        save_summary()
        print(f"Nenhum PDF de entrada encontrado em {root}")
        return summary

    print(f"Lote v{__version__}: {len(files)} PDF(s) | saída: {output_root}")
    for position, input_path in enumerate(files, 1):
        relative = input_path.relative_to(root)
        destination_dir = output_root / relative.parent if recursivo else output_root
        destination_dir.mkdir(parents=True, exist_ok=True)
        output_path = _nome_saida_automatico(destination_dir / input_path.name, target)
        record = {"entrada": str(input_path), "saida": str(output_path), "estado": "pendente"}
        summary["arquivos"].append(record)
        print(f"\n[{position}/{len(files)}] {relative}")
        if output_path.exists() and not sobrescrever:
            record["estado"] = "ignorado_existente"
            print("   Ignorado: o PDF traduzido já existe (use sobrescrever=True para refazer).")
            save_summary()
            continue
        if ignorar_ja_traduzidos and pdf_ja_tem_traducao(input_path):
            record["estado"] = "ignorado_ja_traduzido"
            print("   Ignorado: o PDF já contém comentários de tradução.")
            save_summary()
            continue
        try:
            result = traduzir_pdf(input_path, saida=output_path, retornar_relatorio=True, **opcoes)
            record.update(
                estado=result["estado"],
                relatorio=str(output_path.with_suffix(".relatorio.json")),
                pendencias=str(output_path.with_suffix(".pendencias.json")),
                auditoria=result.get("auditoria"),
                totais=result.get("totais", {}),
            )
        except KeyboardInterrupt:
            record.update(estado="interrompido", erro="Execução interrompida pelo usuário.")
            summary["estado"] = "interrompido"
            save_summary()
            raise
        except Exception as exc:
            record.update(estado="erro", erro=f"{type(exc).__name__}: {exc}")
            print(f"   Falha neste PDF; {'continuando o lote' if continuar_apos_erro else 'interrompendo'}: {record['erro']}")
            save_summary()
            if not continuar_apos_erro:
                summary["estado"] = "erro"
                save_summary()
                raise
        save_summary()

    errors = any(r["estado"] == "erro" for r in summary["arquivos"])
    pending = any(r["estado"] == "concluido_com_pendencias" for r in summary["arquivos"])
    summary["estado"] = "concluido_com_erros" if errors else (
        "concluido_com_pendencias" if pending else "concluido"
    )
    save_summary()
    print(f"\nLote: {summary['estado']} | resumo: {summary_path}")
    return summary


def main():
    """Execução direta mínima: traduz todos os PDFs da pasta ``pdf``."""
    return traduzir_pasta(
        "pdf",
        idioma_origem=DEFAULT_MIXED_LANGUAGES,
        idioma_destino="pt",
        motor_traducao="local",
        modelo_local="nllb_1_3b",
        dispositivo_local="auto",
        precisao_local="float16",
        quantizacao_modelo="float16",
        variante_portugues="pt-BR",
        perfil_terminologico="didatica_matematica",
        proteger_elementos=True,
        traduzir_referencias=False,
        unir_blocos_contiguos=True,
        unir_entre_paginas=True,
        gerar_auditoria=True,
        max_caracteres_trecho=1600,
    )


if __name__ == "__main__":
    main()
