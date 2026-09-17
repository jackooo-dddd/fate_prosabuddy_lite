"""Provider-neutral model interface and DeepSeek implementation."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Any

from openai import OpenAI

from .config import AgentConfig


@dataclass(frozen=True)
class GenerationResult:
    """Normalize generated text and token usage across providers."""

    text: str
    model: str
    input_tokens: int | None = None
    output_tokens: int | None = None
    total_tokens: int | None = None


class LLMBackend(ABC):
    """Minimal interface consumed by the benchmark-independent proof agent."""

    @abstractmethod
    def generate(self, messages: list[dict[str, str]]) -> GenerationResult:
        """Generate one proof or continuation from chat messages."""


class DeepSeekBackend(LLMBackend):
    """Use DeepSeek's OpenAI-compatible chat-completions API."""

    def __init__(self, config: AgentConfig) -> None:
        if not config.deepseek_api_key:
            raise ValueError("DEEPSEEK_API_KEY is empty; configure .env before a real run")
        self.model_name = config.model_name
        self.temperature = config.temperature
        self.max_output_tokens = config.max_output_tokens
        self.client = OpenAI(
            api_key=config.deepseek_api_key,
            base_url=config.deepseek_base_url,
        )

    def generate(self, messages: list[dict[str, str]]) -> GenerationResult:
        request: dict[str, Any] = {
            "model": self.model_name,
            "messages": messages,
            "temperature": self.temperature,
        }
        if self.max_output_tokens is not None:
            request["max_tokens"] = self.max_output_tokens
        response = self.client.chat.completions.create(
            **request,  # type: ignore[arg-type]
        )
        usage: Any = response.usage
        return GenerationResult(
            text=response.choices[0].message.content or "",
            model=response.model or self.model_name,
            input_tokens=getattr(usage, "prompt_tokens", None),
            output_tokens=getattr(usage, "completion_tokens", None),
            total_tokens=getattr(usage, "total_tokens", None),
        )


class ScriptedBackend(LLMBackend):
    """Deterministic backend for unit and local integration tests."""

    def __init__(self, outputs: list[str], model_name: str = "scripted-local") -> None:
        self.outputs = list(outputs)
        self.model_name = model_name
        self.calls = 0

    def generate(self, messages: list[dict[str, str]]) -> GenerationResult:
        del messages
        index = min(self.calls, len(self.outputs) - 1)
        self.calls += 1
        return GenerationResult(self.outputs[index], self.model_name)
